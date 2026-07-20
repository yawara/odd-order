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

/-- **Higman Lemma 12 (p. 89), an actual commutative factor over the
common centre.**

Fix the ambient Singer generator and coordinate on `Φ(P)`.  For a
commutative invariant factor `S`, Higman's `A(n, 1)` classification supplies
a homocyclic exponent-four presentation.  The kernel coordinate is the
prescribed ambient coordinate on the square subgroup, while squaring and
inverse Frobenius force the quotient coordinate and the source relation
`ν = λ²`. -/
theorem exists_commutativeFactorCoordinates_of_ambientFrattiniSinger
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
    (hcommS : IsMulCommutative S) :
    let hPhiInv : IsAInvariant Y.subtype (frattini P) :=
      IsAInvariant.of_characteristic Y.subtype
    let hEA : IsElementaryAbelian 2 ↑(frattini P) :=
      frattini_isElementaryAbelian_of_xiLengthThree
        hP hncomm hmulti hxi hlen hprime
    letI : IsMulCommutative ↑(frattini P) :=
      IsMulCommutative.of_comm hEA.comm
    letI : Module (ZMod 2) (Additive ↑(frattini P)) :=
      hEA.zmodModule
    letI : CommGroup S :=
      { (inferInstance : Group S) with
        mul_comm := hcommS.is_comm.comm }
    let n := Module.finrank (ZMod 2) (Additive ↑(frattini P))
    ∀ (c : Y)
      (ePhi : Additive ↑(frattini P) ≃ₗ[ZMod 2] GaloisField 2 n)
      (nu : GaloisField 2 n),
      ePhi.conj (elabRepresentation 2 hPhiInv.restrict c) =
        Algebra.lmul (ZMod 2) (GaloisField 2 n) nu →
      ∃ (ι : Type) (_ : Fintype ι)
        (ε : S ≃* (ι → Multiplicative (ZMod 4)))
        (hN : Agemo S 2 1 = (frattini P).subgroupOf S),
        let eKernel :=
          homocyclicFourPrescribedKernelCoordinate
            hPhiS.le hN ePhi.toAddEquiv
        let eQuot := homocyclicFourQuotientCoordinate ε eKernel
        let lambda := (frobeniusEquiv (GaloisField 2 n) 2).symm nu
        (∀ z : Additive (Agemo S 2 1),
          eKernel (Additive.ofMul
              ((IsAInvariant.of_characteristic hSinv.restrict).restrict
                c z.toMul)) =
            nu * eKernel z) ∧
        (∀ q : Additive (S ⧸ Agemo S 2 1),
          eQuot (Additive.ofMul
              ((IsAInvariant.of_characteristic hSinv.restrict).quotientMulAutHom
                c q.toMul)) =
            lambda * eQuot q) ∧
        (∀ beta : GaloisField 2 n,
          eKernel ((homocyclicFourSquareEquiv ε).toAdditive
            (eQuot.symm beta)) = beta * beta) ∧
        nu = lambda * lambda := by
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
  letI : CommGroup S :=
    { (inferInstance : Group S) with
      mul_comm := hcommS.is_comm.comm }
  let n := Module.finrank (ZMod 2) (Additive ↑(frattini P))
  intro c ePhi nu hconj
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
  have hmultiS : ∃ x y : S,
      x ∈ involutions S ∧ y ∈ involutions S ∧ x ≠ y :=
    exists_distinct_involutions_subgroup_of_subset hinvS hmulti
  obtain ⟨ι, hι, ⟨ε⟩⟩ :=
    exists_homocyclic_four_of_commutative_xiLengthTwo
      (hP.to_subgroup S) hxiS hlenS hmultiS
  letI : Fintype ι := hι
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
  have hN : Agemo S 2 1 = (frattini P).subgroupOf S :=
    agemo_one_eq_frattini_subgroupOf_of_homocyclic_four
      hcommS ε hinvPhi hEA
  let eKernel : Additive (Agemo S 2 1) ≃+
      GaloisField 2 n :=
    homocyclicFourPrescribedKernelCoordinate
      hPhiS.le hN ePhi.toAddEquiv
  let eQuot : Additive (S ⧸ Agemo S 2 1) ≃+
      GaloisField 2 n :=
    homocyclicFourQuotientCoordinate ε eKernel
  let lambda : GaloisField 2 n :=
    (frobeniusEquiv (GaloisField 2 n) 2).symm nu
  have hcompatPhi : ∀ v,
      ePhi (elabRepresentation 2 hPhiInv.restrict c v) =
        nu * ePhi v := by
    intro v
    have h := DFunLike.congr_fun hconj (ePhi v)
    simpa [LinearEquiv.conj_apply] using h
  have hcompatKernel : ∀ z : Additive (Agemo S 2 1),
      eKernel (Additive.ofMul
          ((IsAInvariant.of_characteristic hSinv.restrict).restrict
            c z.toMul)) =
        nu * eKernel z := by
    intro z
    exact homocyclicFourPrescribedKernelCoordinate_generator_compatible
      hSinv hPhiS.le hN ePhi.toAddEquiv c nu hcompatPhi z
  have hcompatQuot : ∀ q : Additive (S ⧸ Agemo S 2 1),
      eQuot (Additive.ofMul
          ((IsAInvariant.of_characteristic hSinv.restrict).quotientMulAutHom
            c q.toMul)) =
        lambda * eQuot q := by
    intro q
    exact homocyclicFourQuotientCoordinate_generator_compatible
      hSinv.restrict ε eKernel c nu hcompatKernel q
  have hnormal : ∀ beta : GaloisField 2 n,
      eKernel ((homocyclicFourSquareEquiv ε).toAdditive
        (eQuot.symm beta)) = beta * beta := by
    intro beta
    have hbeta := eQuot.apply_symm_apply beta
    change (frobeniusEquiv (GaloisField 2 n) 2).symm
        (eKernel ((homocyclicFourSquareEquiv ε).toAdditive
          (eQuot.symm beta))) = beta at hbeta
    calc
      eKernel ((homocyclicFourSquareEquiv ε).toAdditive
          (eQuot.symm beta)) = beta ^ 2 := by
        rw [← frobeniusEquiv_symm_pow_p (GaloisField 2 n) 2
          (eKernel ((homocyclicFourSquareEquiv ε).toAdditive
            (eQuot.symm beta))), hbeta]
      _ = beta * beta := pow_two beta
  have hnorm : nu = lambda * lambda := by
    change nu =
      (frobeniusEquiv (GaloisField 2 n) 2).symm nu *
        (frobeniusEquiv (GaloisField 2 n) 2).symm nu
    rw [← pow_two, frobeniusEquiv_symm_pow_p]
  exact ⟨ι, hι, ε, hN,
    hcompatKernel, hcompatQuot, hnormal, hnorm⟩

/-- The canonical square equivalence of a commutative exponent-four factor,
with the temporary `CommGroup` instance confined to this definition. -/
def commutativeFactorSquareEquiv
    {S : Type uH} [Group S] [Finite S]
    (hcomm : IsMulCommutative S)
    {index : Type}
    (equivPi : S ≃* (index → Multiplicative (ZMod 4))) :
    (S ⧸ Agemo S 2 1) ≃* Agemo S 2 1 := by
  letI : CommGroup S :=
    { (inferInstance : Group S) with
      mul_comm := hcomm.is_comm.comm }
  exact homocyclicFourSquareEquiv equivPi

/-- Coordinates on one actual commutative invariant factor, measured in a
prescribed ambient Frattini field coordinate.

The public data does not expose a chosen `CommGroup S` instance.  The helper
`commutativeFactorSquareEquiv` reconstructs the canonical square map from
the stored commutativity proof and homocyclic presentation.  This avoids an
instance diamond while retaining the exact provenance of every coordinate. -/
structure CommutativeFactorCoordinateData
    {P : Type uH} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    [IsMulCommutative ↑(frattini P)]
    [Module (ZMod 2) (Additive ↑(frattini P))]
    {S : Subgroup P}
    (hSinv : IsAInvariant Y.subtype S)
    (hPhiS : frattini P ≤ S)
    (c : Y) {n : Nat}
    (ePhi : Additive ↑(frattini P) ≃ₗ[ZMod 2] GaloisField 2 n)
    (nu : GaloisField 2 n) where
  hcomm : IsMulCommutative S
  index : Type
  [fintypeIndex : Fintype index]
  equivPi : S ≃* (index → Multiplicative (ZMod 4))
  hN : Agemo S 2 1 = (frattini P).subgroupOf S
  eKernel : Additive (Agemo S 2 1) ≃+ GaloisField 2 n
  eKernel_eq : ∀ z, eKernel z = ePhi
    (Additive.ofMul
      (homocyclicFourSquareSubgroupEquivFrattini hPhiS hN z.toMul))
  eQuot : Additive (S ⧸ Agemo S 2 1) ≃+ GaloisField 2 n
  eQuot_eq : ∀ q, eQuot q =
    (frobeniusEquiv (GaloisField 2 n) 2).symm
      (eKernel
        ((commutativeFactorSquareEquiv hcomm equivPi).toAdditive q))
  lambda : GaloisField 2 n
  lambda_eq : lambda =
    (frobeniusEquiv (GaloisField 2 n) 2).symm nu
  kernel_compatible : ∀ z,
    eKernel (Additive.ofMul
      ((IsAInvariant.of_characteristic hSinv.restrict).restrict c z.toMul)) =
        nu * eKernel z
  quotient_compatible : ∀ q,
    eQuot (Additive.ofMul
      ((IsAInvariant.of_characteristic hSinv.restrict).quotientMulAutHom
        c q.toMul)) =
      lambda * eQuot q
  square_normal : ∀ beta : GaloisField 2 n,
    eKernel
      ((commutativeFactorSquareEquiv hcomm equivPi).toAdditive
        (eQuot.symm beta)) = beta * beta
  kernel_eigenvalue_eq : nu = lambda * lambda

/-- Coordinates on one actual noncommutative invariant factor, measured in
a prescribed ambient Frattini field coordinate.

The pointwise equality `eKernel_eq` records that the kernel coordinate is the
given ambient coordinate after the canonical group-level identification of
the factor's second lower-central layer with `Φ(P)`.  The remaining fields
retain the actor eigenvalues and the coefficient-one type-A square formula. -/
structure NoncommutativeFactorCoordinateData
    {P : Type uH} [Group P]
    {Y : Subgroup (MulAut P)}
    [IsMulCommutative ↑(frattini P)]
    [Module (ZMod 2) (Additive ↑(frattini P))]
    {S : Subgroup P}
    (hSinv : IsAInvariant Y.subtype S)
    (hPhiS : frattini P ≤ S)
    (c : Y) {n : Nat}
    (ePhi : Additive ↑(frattini P) ≃ₗ[ZMod 2] GaloisField 2 n)
    (nu : GaloisField 2 n) where
  hK1 : lowerCentralLayerKernel S 1 = ⊥
  hterm : lowerCentralTerm S 1 = (frattini P).subgroupOf S
  hSq : LowerCentralSquaresLieInSecond S
  eKernel : Additive (lowerCentralLayer S 1) ≃ₗ[ZMod 2]
    GaloisField 2 n
  eKernel_eq : ∀ v, eKernel v = ePhi
    ((factorLayerOneEquivAmbientFrattini
      hPhiS hK1 hterm).toAdditive v)
  theta : RingAut (GaloisField 2 n)
  eQuot : Additive (lowerCentralLayer S 0) ≃ₗ[ZMod 2]
    GaloisField 2 n
  lambda : GaloisField 2 n
  theta_ne_one : theta ≠ 1
  theta_order_odd : Odd (orderOf theta)
  kernel_compatible : ∀ v,
    eKernel (lowerCentralLayerRepresentation hSinv.restrict 1 c v) =
      nu * eKernel v
  quotient_compatible : ∀ v,
    eQuot (lowerCentralLayerRepresentation hSinv.restrict 0 c v) =
      lambda * eQuot v
  square_normal : ∀ beta : GaloisField 2 n,
    eKernel (lowerCentralSquareMapAdditive S hSq (eQuot.symm beta)) =
      beta * theta beta
  kernel_eigenvalue_eq : nu = lambda * theta lambda

/-- Inclusive coordinates for an actual invariant factor.  The two
constructors deliberately retain their natural carriers: Agemo quotients
for the commutative `A(n, 1)` branch and lower-central layers for the
noncommutative `A(n, φ)` branch. -/
inductive FactorCoordinateData
    {P : Type uH} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    [IsMulCommutative ↑(frattini P)]
    [Module (ZMod 2) (Additive ↑(frattini P))]
    {S : Subgroup P}
    (hSinv : IsAInvariant Y.subtype S)
    (hPhiS : frattini P ≤ S)
    (c : Y) {n : Nat}
    (ePhi : Additive ↑(frattini P) ≃ₗ[ZMod 2] GaloisField 2 n)
    (nu : GaloisField 2 n) where
  | commutative
      (data : CommutativeFactorCoordinateData
        hSinv hPhiS c ePhi nu)
  | noncommutative
      (hncomm : ¬ IsMulCommutative S)
      (data : NoncommutativeFactorCoordinateData
        hSinv hPhiS c ePhi nu)

namespace FactorCoordinateData

/-- The field automorphism in the factor square law; it is the identity in
the commutative branch. -/
def theta
    {P : Type uH} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    [IsMulCommutative ↑(frattini P)]
    [Module (ZMod 2) (Additive ↑(frattini P))]
    {S : Subgroup P}
    {hSinv : IsAInvariant Y.subtype S}
    {hPhiS : frattini P ≤ S}
    {c : Y} {n : Nat}
    {ePhi : Additive ↑(frattini P) ≃ₗ[ZMod 2] GaloisField 2 n}
    {nu : GaloisField 2 n}
    (data : FactorCoordinateData hSinv hPhiS c ePhi nu) :
    RingAut (GaloisField 2 n) :=
  match data with
  | .commutative _ => 1
  | .noncommutative _ d => d.theta

/-- The quotient eigenvalue in either factor branch. -/
def lambda
    {P : Type uH} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    [IsMulCommutative ↑(frattini P)]
    [Module (ZMod 2) (Additive ↑(frattini P))]
    {S : Subgroup P}
    {hSinv : IsAInvariant Y.subtype S}
    {hPhiS : frattini P ≤ S}
    {c : Y} {n : Nat}
    {ePhi : Additive ↑(frattini P) ≃ₗ[ZMod 2] GaloisField 2 n}
    {nu : GaloisField 2 n}
    (data : FactorCoordinateData hSinv hPhiS c ePhi nu) :
    GaloisField 2 n :=
  match data with
  | .commutative d => d.lambda
  | .noncommutative _ d => d.lambda

/-- Both branches satisfy Higman's common source equation
`ν = λ θ(λ)`. -/
theorem kernel_eigenvalue_eq
    {P : Type uH} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    [IsMulCommutative ↑(frattini P)]
    [Module (ZMod 2) (Additive ↑(frattini P))]
    {S : Subgroup P}
    {hSinv : IsAInvariant Y.subtype S}
    {hPhiS : frattini P ≤ S}
    {c : Y} {n : Nat}
    {ePhi : Additive ↑(frattini P) ≃ₗ[ZMod 2] GaloisField 2 n}
    {nu : GaloisField 2 n}
    (data : FactorCoordinateData hSinv hPhiS c ePhi nu) :
    nu = data.lambda * data.theta data.lambda := by
  cases data with
  | commutative d =>
      simpa [lambda, theta] using d.kernel_eigenvalue_eq
  | noncommutative _ d =>
      simpa [lambda, theta] using d.kernel_eigenvalue_eq

end FactorCoordinateData

/-- **Higman Lemma 12 (p. 89), inclusive coordinates on one actual
factor.**

Over a fixed ambient Singer datum, every proper invariant factor above
`Φ(P)` carries either the commutative `A(n, 1)` coordinates or the
noncommutative `A(n, φ)` coordinates.  The tagged result preserves the
natural kernel and quotient carriers in both branches. -/
theorem exists_factorCoordinates_of_ambientFrattiniSinger
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
    (hStop : S < (⊤ : Subgroup P)) :
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
      Nonempty (FactorCoordinateData hSinv hPhiS.le c ePhi nu) := by
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
  by_cases hcommS : IsMulCommutative S
  · letI : CommGroup S :=
      { (inferInstance : Group S) with
        mul_comm := hcommS.is_comm.comm }
    obtain ⟨ι, hι, ε, hN, hcompatKernel, hcompatQuot,
        hnormal, hnorm⟩ :=
      exists_commutativeFactorCoordinates_of_ambientFrattiniSinger
        hP hncomm hmulti hxi hlen hprime
        hSinv hPhiS hStop hcommS c ePhi nu hconj
    letI : Fintype ι := hι
    let eKernel : Additive (Agemo S 2 1) ≃+
        GaloisField 2 n :=
      homocyclicFourPrescribedKernelCoordinate
        hPhiS.le hN ePhi.toAddEquiv
    let eQuot : Additive (S ⧸ Agemo S 2 1) ≃+
        GaloisField 2 n :=
      homocyclicFourQuotientCoordinate ε eKernel
    let lambda : GaloisField 2 n :=
      (frobeniusEquiv (GaloisField 2 n) 2).symm nu
    let data : CommutativeFactorCoordinateData
        hSinv hPhiS.le c ePhi nu := {
      hcomm := hcommS
      index := ι
      equivPi := ε
      hN := hN
      eKernel := eKernel
      eKernel_eq := fun _ => rfl
      eQuot := eQuot
      eQuot_eq := fun _ => rfl
      lambda := lambda
      lambda_eq := rfl
      kernel_compatible := hcompatKernel
      quotient_compatible := hcompatQuot
      square_normal := hnormal
      kernel_eigenvalue_eq := hnorm }
    exact ⟨FactorCoordinateData.commutative data⟩
  · obtain ⟨hK1, hterm, theta, eQuot, lambda,
        hthetaNe, hthetaOdd, hcompatKernel, hcompatQuot,
        hnormal, hnorm⟩ :=
      exists_noncommutativeFactorCoordinates_of_ambientFrattiniSinger
        hP hncomm hmulti hxi hlen hprime
        hSinv hPhiS hStop hcommS c ePhi nu hnTwo hcgen
        hnuPrimitive hconj
    let hxiS : IsXiActor hSinv.restrict.range :=
      restricted_range_isXiActor hxi hSinv
    let hlenS : HasXiLengthTwo hSinv.restrict.range.subtype :=
      restricted_range_hasXiLengthTwo_of_xiLengthThree
        hP hncomm hxi hlen hEA hSinv hPhiS hStop
    let hSq : LowerCentralSquaresLieInSecond S :=
      lowerCentralSquaresLieInSecond_of_agemo_eq S
        (agemo_one_eq_lowerCentralTerm_one
          (hP.to_subgroup S) hcommS hxiS hlenS)
    let eKernel : Additive (lowerCentralLayer S 1) ≃ₗ[ZMod 2]
        GaloisField 2 n :=
      (factorLayerOneLinearEquivAmbientFrattini
        hEA hPhiS.le hK1 hterm).trans ePhi
    let data : NoncommutativeFactorCoordinateData
        hSinv hPhiS.le c ePhi nu := {
      hK1 := hK1
      hterm := hterm
      hSq := hSq
      eKernel := eKernel
      eKernel_eq := fun _ => rfl
      theta := theta
      eQuot := eQuot
      lambda := lambda
      theta_ne_one := hthetaNe
      theta_order_odd := hthetaOdd
      kernel_compatible := hcompatKernel
      quotient_compatible := hcompatQuot
      square_normal := hnormal
      kernel_eigenvalue_eq := hnorm }
    exact ⟨FactorCoordinateData.noncommutative hcommS data⟩

/-- **Higman Lemma 12 (p. 89), factor-pair coordinates over one common
Singer datum.**

The ambient generator, Frattini coordinate, and primitive scalar are chosen
once and used for both actual invariant factors.  No commutativity
assumption is made on either factor, so the returned tagged pair covers all
four commutative/noncommutative combinations and satisfies the common source
equations `ν = λ θ(λ) = μ φ(μ)`. -/
theorem exists_factorPairCoordinates_of_xiLengthThree
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
    {S T : Subgroup P}
    (hSinv : IsAInvariant Y.subtype S)
    (hPhiS : frattini P < S)
    (hStop : S < (⊤ : Subgroup P))
    (hTinv : IsAInvariant Y.subtype T)
    (hPhiT : frattini P < T)
    (hTtop : T < (⊤ : Subgroup P)) :
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
    ∃ (c : Y)
      (ePhi : Additive ↑(frattini P) ≃ₗ[ZMod 2] GaloisField 2 n)
      (nu : GaloisField 2 n)
      (left : FactorCoordinateData hSinv hPhiS.le c ePhi nu)
      (right : FactorCoordinateData hTinv hPhiT.le c ePhi nu),
      2 ≤ n ∧
      (∀ g : Y, g ∈ Subgroup.zpowers c) ∧
      IsPrimitiveRoot nu (2 ^ n - 1) ∧
      ePhi.conj (elabRepresentation 2 hPhiInv.restrict c) =
        Algebra.lmul (ZMod 2) (GaloisField 2 n) nu ∧
      nu = left.lambda * left.theta left.lambda ∧
      nu = right.lambda * right.theta right.lambda := by
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
  obtain ⟨c, ePhi, nu, _b, hnTwo, hcgen, hnuPrimitive,
      hconj, _hadjoin, _hbasis⟩ :=
    exists_ambientFrattiniSingerCoordinates_of_xiLengthThree
      hP hncomm hmulti hxi hlen hprime
  obtain ⟨left⟩ :=
    exists_factorCoordinates_of_ambientFrattiniSinger
      hP hncomm hmulti hxi hlen hprime
      hSinv hPhiS hStop c ePhi nu hnTwo hcgen
      hnuPrimitive hconj
  obtain ⟨right⟩ :=
    exists_factorCoordinates_of_ambientFrattiniSinger
      hP hncomm hmulti hxi hlen hprime
      hTinv hPhiT hTtop c ePhi nu hnTwo hcgen
      hnuPrimitive hconj
  exact ⟨c, ePhi, nu, left, right,
    hnTwo, hcgen, hnuPrimitive, hconj,
    left.kernel_eigenvalue_eq, right.kernel_eigenvalue_eq⟩

/-- **Higman Lemma 12 (pp. 89--90), coordinates on the actual
complementary factors.**

This packages the complementary normal invariant Frattini preimages, their
inclusive type-A models, and their coordinates over one ambient Singer
datum.  In particular, the returned `factors` retains
`left ⊓ right = Φ(P)` and `left ⊔ right = P`, while the tagged coordinate
data covers every commutative/noncommutative combination. -/
theorem exists_complementaryFactorCoordinates_of_xiLengthThree
    {P : Type uH} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hncomm : ¬ IsMulCommutative P)
    (hmulti : ∃ x y : P,
      x ∈ involutions P ∧ y ∈ involutions P ∧ x ≠ y)
    (hxi : IsXiActor Y)
    (hlen : HasXiLengthThree Y.subtype)
    (hprime : ∀ p : Nat, p.Prime → p ∣ Nat.card Y →
      p ∣ (involutions P).ncard) :
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
    ∃ (factors : XiLengthThreeTypeAFactorData P Y)
      (c : Y)
      (ePhi : Additive ↑(frattini P) ≃ₗ[ZMod 2] GaloisField 2 n)
      (nu : GaloisField 2 n)
      (left : FactorCoordinateData
        factors.left_invariant factors.frattini_lt_left.le c ePhi nu)
      (right : FactorCoordinateData
        factors.right_invariant factors.frattini_lt_right.le c ePhi nu),
      2 ≤ n ∧
      (∀ g : Y, g ∈ Subgroup.zpowers c) ∧
      IsPrimitiveRoot nu (2 ^ n - 1) ∧
      ePhi.conj (elabRepresentation 2 hPhiInv.restrict c) =
        Algebra.lmul (ZMod 2) (GaloisField 2 n) nu ∧
      nu = left.lambda * left.theta left.lambda ∧
      nu = right.lambda * right.theta right.lambda := by
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
  obtain ⟨factors⟩ :=
    xiLengthThreeTypeAFactorData_exists
      hP hncomm hmulti hxi hlen hprime
  obtain ⟨c, ePhi, nu, left, right,
      hnTwo, hcgen, hnuPrimitive, hconj, hleft, hright⟩ :=
    exists_factorPairCoordinates_of_xiLengthThree
      hP hncomm hmulti hxi hlen hprime
      factors.left_invariant factors.frattini_lt_left
      factors.left_lt_top
      factors.right_invariant factors.frattini_lt_right
      factors.right_lt_top
  exact ⟨factors, c, ePhi, nu, left, right,
    hnTwo, hcgen, hnuPrimitive, hconj, hleft, hright⟩

/-- **Higman Lemma 12 (p. 89), paired noncommutative factor
coordinates.**

Choose the Singer datum on the ambient `Φ(P)` once, then use that same
generator, field coordinate, and primitive scalar for both invariant
factors.  Both kernel coordinates are therefore prescribed by the same
`ePhi`, while the two quotient normal forms give Higman's source equations
`ν = λ θ(λ) = μ φ(μ)`. -/
theorem exists_noncommutativePairCoordinates_of_xiLengthThree
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
    {S T : Subgroup P}
    (hSinv : IsAInvariant Y.subtype S)
    (hPhiS : frattini P < S)
    (hStop : S < (⊤ : Subgroup P))
    (hncommS : ¬ IsMulCommutative S)
    (hTinv : IsAInvariant Y.subtype T)
    (hPhiT : frattini P < T)
    (hTtop : T < (⊤ : Subgroup P))
    (hncommT : ¬ IsMulCommutative T) :
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
    ∃ (c : Y)
      (ePhi : Additive ↑(frattini P) ≃ₗ[ZMod 2] GaloisField 2 n)
      (nu : GaloisField 2 n)
      (left : NoncommutativeFactorCoordinateData
        hSinv hPhiS.le c ePhi nu)
      (right : NoncommutativeFactorCoordinateData
        hTinv hPhiT.le c ePhi nu),
      2 ≤ n ∧
      (∀ g : Y, g ∈ Subgroup.zpowers c) ∧
      IsPrimitiveRoot nu (2 ^ n - 1) ∧
      ePhi.conj (elabRepresentation 2 hPhiInv.restrict c) =
        Algebra.lmul (ZMod 2) (GaloisField 2 n) nu ∧
      nu = left.lambda * left.theta left.lambda ∧
      nu = right.lambda * right.theta right.lambda := by
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
  obtain ⟨c, ePhi, nu, _b, hnTwo, hcgen, hnuPrimitive,
      hconj, _hadjoin, _hbasis⟩ :=
    exists_ambientFrattiniSingerCoordinates_of_xiLengthThree
      hP hncomm hmulti hxi hlen hprime
  obtain ⟨hK1S, htermS, theta, eQuotS, lambda,
      hthetaNe, hthetaOdd, hcompatKernelS, hcompatQuotS,
      hnormalS, hnormS⟩ :=
    exists_noncommutativeFactorCoordinates_of_ambientFrattiniSinger
      hP hncomm hmulti hxi hlen hprime
      hSinv hPhiS hStop hncommS c ePhi nu hnTwo hcgen
      hnuPrimitive hconj
  obtain ⟨hK1T, htermT, phi, eQuotT, mu,
      hphiNe, hphiOdd, hcompatKernelT, hcompatQuotT,
      hnormalT, hnormT⟩ :=
    exists_noncommutativeFactorCoordinates_of_ambientFrattiniSinger
      hP hncomm hmulti hxi hlen hprime
      hTinv hPhiT hTtop hncommT c ePhi nu hnTwo hcgen
      hnuPrimitive hconj
  let hxiS : IsXiActor hSinv.restrict.range :=
    restricted_range_isXiActor hxi hSinv
  let hlenS : HasXiLengthTwo hSinv.restrict.range.subtype :=
    restricted_range_hasXiLengthTwo_of_xiLengthThree
      hP hncomm hxi hlen hEA hSinv hPhiS hStop
  let hSqS : LowerCentralSquaresLieInSecond S :=
    lowerCentralSquaresLieInSecond_of_agemo_eq S
      (agemo_one_eq_lowerCentralTerm_one
        (hP.to_subgroup S) hncommS hxiS hlenS)
  let eKernelS : Additive (lowerCentralLayer S 1) ≃ₗ[ZMod 2]
      GaloisField 2 n :=
    (factorLayerOneLinearEquivAmbientFrattini
      hEA hPhiS.le hK1S htermS).trans ePhi
  let hxiT : IsXiActor hTinv.restrict.range :=
    restricted_range_isXiActor hxi hTinv
  let hlenT : HasXiLengthTwo hTinv.restrict.range.subtype :=
    restricted_range_hasXiLengthTwo_of_xiLengthThree
      hP hncomm hxi hlen hEA hTinv hPhiT hTtop
  let hSqT : LowerCentralSquaresLieInSecond T :=
    lowerCentralSquaresLieInSecond_of_agemo_eq T
      (agemo_one_eq_lowerCentralTerm_one
        (hP.to_subgroup T) hncommT hxiT hlenT)
  let eKernelT : Additive (lowerCentralLayer T 1) ≃ₗ[ZMod 2]
      GaloisField 2 n :=
    (factorLayerOneLinearEquivAmbientFrattini
      hEA hPhiT.le hK1T htermT).trans ePhi
  let left : NoncommutativeFactorCoordinateData
      hSinv hPhiS.le c ePhi nu := {
    hK1 := hK1S
    hterm := htermS
    hSq := hSqS
    eKernel := eKernelS
    eKernel_eq := fun _ => rfl
    theta := theta
    eQuot := eQuotS
    lambda := lambda
    theta_ne_one := hthetaNe
    theta_order_odd := hthetaOdd
    kernel_compatible := hcompatKernelS
    quotient_compatible := hcompatQuotS
    square_normal := hnormalS
    kernel_eigenvalue_eq := hnormS }
  let right : NoncommutativeFactorCoordinateData
      hTinv hPhiT.le c ePhi nu := {
    hK1 := hK1T
    hterm := htermT
    hSq := hSqT
    eKernel := eKernelT
    eKernel_eq := fun _ => rfl
    theta := phi
    eQuot := eQuotT
    lambda := mu
    theta_ne_one := hphiNe
    theta_order_odd := hphiOdd
    kernel_compatible := hcompatKernelT
    quotient_compatible := hcompatQuotT
    square_normal := hnormalT
    kernel_eigenvalue_eq := hnormT }
  exact ⟨c, ePhi, nu, left, right,
    hnTwo, hcgen, hnuPrimitive, hconj, hnormS, hnormT⟩

end

end OddOrder.Higman.Suzuki2Groups
