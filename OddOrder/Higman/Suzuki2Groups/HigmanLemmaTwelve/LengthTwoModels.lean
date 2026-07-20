/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaTwelve.QuotientTwoStep
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaEleven
import OddOrder.Higman.Suzuki2Groups.HigmanIdempotentAction
import OddOrder.Peterfalvi.Appendices.Suzuki.SemilinearModel

/-!
# Higman's Lemma 12: models for the ξ-length-two factors

G. Higman, “Suzuki 2-groups,” *Illinois Journal of Mathematics* 7 (1963),
pp. 89--90.

Higman extends the notation `A(n, φ)` to include the abelian case
`A(n, 1) = C₄ⁿ` immediately before Lemma 12. Peterfalvi's later
`TypeAData` deliberately describes only the noncommutative case and hence
requires `φ ≠ 1`. This leaf keeps those meanings distinct: the inclusive
`XiLengthTwoTypeAData` is the source-facing carrier for the two factors in
Lemma 12, while `TypeAData` maps into it by forgetting only nontriviality.

The restricted actor bridges below transfer cyclicity, involution
transitivity, and Higman's prime-support condition to an invariant factor.
Thus every noncommutative lifted factor is classified by Lemma 11.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

open OddOrder.GroupTheory
open OddOrder.GroupTheory.Suzuki2Group
open OddOrder.Isaacs.Ch03
open OddOrder.Peterfalvi.Appendices.Suzuki2Groups

universe uP uF uQ uE

private theorem mulAutTwistedNorm_injective_of_odd_order
    {G : Type*} [CommGroup G]
    (sigma : MulAut G) (hsigma : Odd (orderOf sigma))
    (hsq : Function.Injective fun x : G => x ^ 2) :
    Function.Injective fun x : G => x * sigma x := by
  intro x y hxy
  let z : G := x * y⁻¹
  have hz : z * sigma z = 1 := by
    calc
      z * sigma z = (x * sigma x) * (y * sigma y)⁻¹ := by
        simp only [z, map_mul, map_inv, mul_inv_rev]
        simp only [mul_assoc, mul_comm, mul_left_comm]
      _ = 1 := by
        change x * sigma x = y * sigma y at hxy
        rw [hxy, mul_inv_cancel]
  have hsigmaZ : sigma z = z⁻¹ := eq_inv_of_mul_eq_one_right hz
  have hsigmaSqZ : (sigma ^ 2) z = z := by
    simp only [pow_two, MulAut.mul_apply, hsigmaZ, map_inv, inv_inv]
  have hiterate (j : ℕ) : ((sigma ^ 2) ^ j) z = z := by
    induction j with
    | zero => simp
    | succ j ih =>
        rw [pow_succ', MulAut.mul_apply, ih, hsigmaSqZ]
  obtain ⟨k, hk⟩ := hsigma
  have hevenFix : (sigma ^ (2 * k)) z = z := by
    simpa only [pow_mul] using hiterate k
  have horderFix : (sigma ^ orderOf sigma) z = z := by
    rw [pow_orderOf_eq_one]
    rfl
  have hsigmaFix : sigma z = z := by
    rw [hk, show 2 * k + 1 = (2 * k) + 1 by rfl,
      pow_succ', MulAut.mul_apply, hevenFix] at horderFix
    exact horderFix
  have hzsq : z ^ 2 = 1 := by
    simpa [pow_two, hsigmaFix] using hz
  have hzOne : z = 1 := hsq (by simpa using hzsq)
  simpa [z, mul_inv_eq_one] using hzOne

private theorem mulAutTwistedNorm_bijective_of_odd_order
    {G : Type*} [CommGroup G] [Finite G]
    (sigma : MulAut G) (hsigma : Odd (orderOf sigma))
    (hsq : Function.Injective fun x : G => x ^ 2) :
    Function.Bijective fun x : G => x * sigma x :=
  (mulAutTwistedNorm_injective_of_odd_order sigma hsigma hsq).bijective_of_finite

/-- **Higman Lemma 12 (p. 89), type-A basis rescaling.**

If `phi` has odd order, the twisted norm `u ↦ u * phi(u)` is a
permutation of the nonzero elements of a finite field of characteristic two.
This is the precise reason that the central conjugate basis can be prescribed
first and the quotient basis rescaled afterwards.  The case `phi = 1`, used
for the abelian group `A(n, 1)`, is included. -/
theorem typeAUnitNorm_bijective
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (phi : RingAut F) (hphi : Odd (orderOf phi)) :
    Function.Bijective fun u : Fˣ => u *
      OddOrder.Peterfalvi.Appendices.Suzuki.fieldRingAutOnUnits F phi u := by
  let sigma : MulAut Fˣ :=
    OddOrder.Peterfalvi.Appendices.Suzuki.fieldRingAutOnUnits F phi
  have hsigmaDvd : orderOf sigma ∣ orderOf phi :=
    orderOf_map_dvd
      (OddOrder.Peterfalvi.Appendices.Suzuki.fieldRingAutOnUnits F) phi
  have hsigma : Odd (orderOf sigma) := hphi.of_dvd_nat hsigmaDvd
  apply mulAutTwistedNorm_bijective_of_odd_order sigma hsigma
  intro u v huv
  apply Units.ext
  have huv' : (u : F) ^ 2 = (v : F) ^ 2 := congrArg Units.val huv
  exact CharTwo.sq_injective huv'

/-- Every prescribed nonzero central scaling is `u * phi(u)` for a nonzero
quotient-basis scaling `u`. -/
theorem exists_ne_zero_mul_apply_eq_of_typeA
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (phi : RingAut F) (hphi : Odd (orderOf phi))
    (v : F) (hv : v ≠ 0) :
    ∃ u : F, u ≠ 0 ∧ u * phi u = v := by
  let vUnit : Fˣ := Units.mk0 v hv
  obtain ⟨u, hu⟩ := (typeAUnitNorm_bijective phi hphi).2 vUnit
  refine ⟨(u : F), Units.ne_zero u, ?_⟩
  have huval := congrArg Units.val hu
  simpa [vUnit,
    OddOrder.Peterfalvi.Appendices.Suzuki.fieldRingAutOnUnits_apply_val]
    using huval

/-- Absorb a nonzero type-A coefficient by rescaling only the quotient
coordinate, leaving a prescribed kernel coordinate unchanged. -/
theorem exists_typeANormalForm_coefficient_one
    {V : Type*} {W : Type*}
    [AddCommGroup V] [AddCommGroup W]
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (eZero : V ≃+ F) (eKernel : W ≃+ F)
    (q : V → W) (theta : RingAut F)
    (htheta : Odd (orderOf theta))
    (epsilon : F) (hepsilon : epsilon ≠ 0)
    (hformula : ∀ alpha : F,
      eKernel (q (eZero.symm alpha)) =
        epsilon * (alpha * theta alpha)) :
    ∃ eZero' : V ≃+ F, ∀ beta : F,
      eKernel (q (eZero'.symm beta)) = beta * theta beta := by
  obtain ⟨u, hu, hunorm⟩ :=
    exists_ne_zero_mul_apply_eq_of_typeA theta htheta epsilon hepsilon
  let uUnit : Fˣ := Units.mk0 u hu
  let scale : F ≃+ F :=
    (uUnit.mulLeftLinearEquiv F F).toAddEquiv
  let eZero' : V ≃+ F := eZero.trans scale
  refine ⟨eZero', ?_⟩
  intro beta
  let alpha : F := scale.symm beta
  have hscale : u * alpha = beta := by
    have h := scale.apply_symm_apply beta
    change u * alpha = beta at h
    exact h
  calc
    eKernel (q (eZero'.symm beta)) =
        epsilon * (alpha * theta alpha) := by
      change eKernel (q (eZero.symm (scale.symm beta))) = _
      exact hformula alpha
    _ = beta * theta beta := by
      rw [← hunorm, ← hscale, map_mul]
      ring

/-- The composite of the bracket-normalization Frobenius shift and the
anchored-trace Frobenius shift, in their actual order of application. -/
noncomputable def combinedKernelFrobeniusShift
    (F : Type uF) [Field F] [Finite F] [Algebra (ZMod 2) F]
    (s s₀ : Nat) : F ≃ₐ[ZMod 2] F :=
  ((FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) F) ^ s).trans
    ((FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) F) ^ s₀)

/-- The composite is the single Frobenius power with the summed exponent. -/
theorem combinedKernelFrobeniusShift_eq_pow_add
    (F : Type uF) [Field F] [Finite F] [Algebra (ZMod 2) F]
    (s s₀ : Nat) :
    combinedKernelFrobeniusShift F s s₀ =
      (FiniteField.frobeniusAlgEquivOfAlgebraic
        (ZMod 2) F) ^ (s + s₀) := by
  let frob := FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) F
  rw [combinedKernelFrobeniusShift]
  change frob ^ s₀ * frob ^ s = frob ^ (s + s₀)
  rw [← pow_add, add_comm]

/-- Two successive equality-tracked kernel-coordinate shifts compose to the
single algebra automorphism used when restoring the prescribed coordinate. -/
theorem secondLayerCoordinate_eq_trans_combinedKernelFrobeniusShift
    {F : Type uF} {V : Type uE}
    [Field F] [Finite F] [Algebra (ZMod 2) F]
    [AddCommGroup V] [Module (ZMod 2) V]
    (eKernel eNormalized eShifted : V ≃ₗ[ZMod 2] F)
    (s s₀ : Nat)
    (hNormalized : eNormalized = eKernel.trans
      (((FiniteField.frobeniusAlgEquivOfAlgebraic
        (ZMod 2) F) ^ s).toLinearEquiv))
    (hShifted : eShifted = eNormalized.trans
      (((FiniteField.frobeniusAlgEquivOfAlgebraic
        (ZMod 2) F) ^ s₀).toLinearEquiv)) :
    eShifted = eKernel.trans
      (combinedKernelFrobeniusShift F s s₀).toLinearEquiv := by
  subst eNormalized
  subst eShifted
  rfl

/-- The combined kernel Frobenius shift commutes with every Frobenius power
appearing as the type-A automorphism. -/
theorem combinedKernelFrobeniusShift_commutes_frobeniusPower
    {F : Type uF} [Field F] [Finite F] [CharP F 2]
    [Algebra (ZMod 2) F]
    (s s₀ r : Nat) (x : F) :
    combinedKernelFrobeniusShift F s s₀
        (((frobeniusEquiv F 2) ^ r) x) =
      ((frobeniusEquiv F 2) ^ r)
        (combinedKernelFrobeniusShift F s s₀ x) := by
  rw [← iterateFrobeniusEquiv_eq_pow]
  simp only [iterateFrobeniusEquiv_def, map_pow]

/-- Package the exact automorphism and commutation proof produced by the two
shift-tracking APIs. -/
theorem exists_combinedKernelFrobeniusShift
    {F : Type uF} {V : Type uE}
    [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
    [AddCommGroup V] [Module (ZMod 2) V]
    (eKernel eNormalized eShifted : V ≃ₗ[ZMod 2] F)
    (s s₀ : Fin (Module.finrank (ZMod 2) F))
    (r : Nat)
    (hNormalized : eNormalized = eKernel.trans
      (((FiniteField.frobeniusAlgEquivOfAlgebraic
        (ZMod 2) F) ^ s.val).toLinearEquiv))
    (hShifted : eShifted = eNormalized.trans
      (((FiniteField.frobeniusAlgEquivOfAlgebraic
        (ZMod 2) F) ^ s₀.val).toLinearEquiv)) :
    ∃ sigma : F ≃ₐ[ZMod 2] F,
      eShifted = eKernel.trans sigma.toLinearEquiv ∧
      ∀ x : F,
        sigma (((frobeniusEquiv F 2) ^ r) x) =
          ((frobeniusEquiv F 2) ^ r) (sigma x) := by
  refine ⟨combinedKernelFrobeniusShift F s.val s₀.val, ?_, ?_⟩
  · exact secondLayerCoordinate_eq_trans_combinedKernelFrobeniusShift
      eKernel eNormalized eShifted s.val s₀.val hNormalized hShifted
  · exact combinedKernelFrobeniusShift_commutes_frobeniusPower
      s.val s₀.val r

local instance combinedShiftLayerCommGroup
    (H : Type uP) [Group H] (i : Nat) :
    CommGroup (lowerCentralLayer H i) :=
  { (inferInstance : Group (lowerCentralLayer H i)) with
    mul_comm := (lowerCentralLayer_isElementaryAbelian H i).comm }

noncomputable local instance combinedShiftLayerModule
    (H : Type uP) [Group H] (i : Nat) :
    Module (ZMod 2) (Additive (lowerCentralLayer H i)) :=
  lowerCentralLayerZmodModule H i

/-- The two tracked shifts provide exactly the automorphism and commutation
hypothesis needed to restore the original prescribed kernel coordinate in the
type-A normal form. -/
theorem exists_typeANormalForm_preserving_original_kernel_of_two_shifts
    {H : Type uP} [Group H]
    {F : Type uF} [Field F] [Finite F] [CharP F 2]
    [Algebra (ZMod 2) F]
    (hSq : LowerCentralSquaresLieInSecond H)
    (eZero : Additive (lowerCentralLayer H 0) ≃ₗ[ZMod 2] F)
    (eKernel eNormalized eShifted :
      Additive (lowerCentralLayer H 1) ≃ₗ[ZMod 2] F)
    (s s₀ : Fin (Module.finrank (ZMod 2) F))
    (r : Nat)
    (hNormalized : eNormalized = eKernel.trans
      (((FiniteField.frobeniusAlgEquivOfAlgebraic
        (ZMod 2) F) ^ s.val).toLinearEquiv))
    (hShifted : eShifted = eNormalized.trans
      (((FiniteField.frobeniusAlgEquivOfAlgebraic
        (ZMod 2) F) ^ s₀.val).toLinearEquiv))
    (epsilon : F)
    (hformula : ∀ alpha : F,
      eShifted
          (lowerCentralSquareMapAdditive H hSq (eZero.symm alpha)) =
        epsilon * (alpha * ((frobeniusEquiv F 2) ^ r) alpha)) :
    ∃ eZero' : Additive (lowerCentralLayer H 0) ≃ₗ[ZMod 2] F,
      ∃ epsilon' : F,
        ∀ beta : F,
          eKernel
              (lowerCentralSquareMapAdditive H hSq (eZero'.symm beta)) =
            epsilon' * (beta * ((frobeniusEquiv F 2) ^ r) beta) := by
  obtain ⟨sigma, hcoordinate, hcomm⟩ :=
    exists_combinedKernelFrobeniusShift
      eKernel eNormalized eShifted s s₀ r hNormalized hShifted
  apply exists_typeANormalForm_preserving_kernel_coordinate
    hSq eZero eKernel sigma ((frobeniusEquiv F 2) ^ r)
    hcomm epsilon
  intro alpha
  rw [← hcoordinate]
  exact hformula alpha

/-- Honest model data for a ξ-length-two Higman factor `A(n, φ)`.

Unlike Peterfalvi's noncommutative `TypeAData`, this source-facing carrier
allows `φ = 1`, which is Higman's abelian case `A(n, 1) = C₄ⁿ`. -/
structure XiLengthTwoTypeAData (P : Type uP) [Group P] where
  F : Type uF
  [fieldF : Field F]
  [finiteF : Finite F]
  [charTwoF : CharP F 2]
  parameter : ℕ
  parameter_pos : 0 < parameter
  card_field : Nat.card F = 2 ^ parameter
  phi : RingAut F
  phi_orderOf_odd : Odd (orderOf phi)
  equivModel : P ≃* TypeAModel phi

/-- A group has an inclusive ξ-length-two `A(n, φ)` model. -/
def IsXiLengthTwoTypeA (P : Type uP) [Group P] : Prop :=
  Nonempty (XiLengthTwoTypeAData.{uP, uF} P)

namespace XiLengthTwoTypeAData

/-- Forget only the nontriviality of `φ` from Peterfalvi's noncommutative
type-A data. -/
def ofTypeAData
    {P : Type uP} [Group P]
    (d : TypeAData.{uP, uF} P) :
    XiLengthTwoTypeAData.{uP, uF} P where
  F := d.F
  fieldF := d.fieldF
  finiteF := d.finiteF
  charTwoF := d.charTwoF
  parameter := d.parameter
  parameter_pos := d.parameter_pos
  card_field := d.card_field
  phi := d.phi
  phi_orderOf_odd := d.phi_orderOf_odd
  equivModel := d.equivModel

/-- Build inclusive `A(n, φ)` data from an actual central extension whose
square coordinate is `a ↦ a * φ(a)`. This is the source-faithful
`φ = 1` extension of `TypeAData.ofExtension`. -/
noncomputable def ofExtension
    {P : Type uP} [Group P]
    {F : Type uF} [Field F] [Finite F] [CharP F 2]
    (parameter : ℕ) (parameter_pos : 0 < parameter)
    (card_field : Nat.card F = 2 ^ parameter)
    (phi : RingAut F)
    (phi_orderOf_odd : Odd (orderOf phi))
    (S : GroupExtension (Multiplicative F) P (Multiplicative F))
    (hcentral : S.inl.range ≤ Subgroup.center P)
    (hsq : ∀ x : P, x ^ 2 =
      S.inl (Multiplicative.ofAdd
        (typeAQuadraticMap phi (S.rightHom x).toAdd))) :
    XiLengthTwoTypeAData P := by
  letI : Algebra (ZMod 2) F := ZMod.algebra F 2
  let q := typeAQuadraticMap phi
  let basis := Module.finBasis (ZMod 2) F
  let extEquiv : S.Equiv (QuadraticExtension.extension q basis) := by
    apply GroupExtension.equivOfCommonSquareMap S
      (QuadraticExtension.extension q basis) hcentral
      (QuadraticExtension.range_inl_le_center q basis) q basis
    · exact hsq
    · intro x
      change x ^ 2 =
        (QuadraticExtension.extension q basis).inl
          (Multiplicative.ofAdd (q x.quotient))
      exact QuadraticExtension.sq_eq_inl_q q basis x
  exact
    { F := F
      parameter := parameter
      parameter_pos := parameter_pos
      card_field := card_field
      phi := phi
      phi_orderOf_odd := phi_orderOf_odd
      equivModel := extEquiv.toMulEquiv }

/-- Absorb a nonzero scalar in an `A(n, φ)` square formula into the kernel
coordinate, allowing `φ = 1`. -/
noncomputable def ofScaledSquareCoordinates
    {P : Type uP} [Group P]
    {F : Type uF} [Field F] [Finite F] [CharP F 2]
    (parameter : ℕ) (parameter_pos : 0 < parameter)
    (card_field : Nat.card F = 2 ^ parameter)
    (phi : RingAut F)
    (phi_orderOf_odd : Odd (orderOf phi))
    (N : Subgroup P) [N.Normal]
    (left : Multiplicative F ≃* N)
    (right : P ⧸ N ≃* Multiplicative F)
    (hcentral : N ≤ Subgroup.center P)
    (epsilon : F) (hepsilon : epsilon ≠ 0)
    (hsq : ∀ x : P, x ^ 2 =
      left (Multiplicative.ofAdd
        (epsilon *
          ((right (QuotientGroup.mk' N x)).toAdd *
            phi (right (QuotientGroup.mk' N x)).toAdd)))) :
    XiLengthTwoTypeAData P := by
  let epsilonUnit : Fˣ := Units.mk0 epsilon hepsilon
  let scaleAdd : F ≃+ F :=
    (epsilonUnit.mulLeftLinearEquiv F F).toAddEquiv
  let scale : Multiplicative F ≃* Multiplicative F :=
    AddEquiv.toMultiplicative scaleAdd
  let left' : Multiplicative F ≃* N := scale.trans left
  let S : GroupExtension (Multiplicative F) P (Multiplicative F) :=
    GroupExtension.ofNormalSubgroupCoordinates N left' right
  apply ofExtension parameter parameter_pos card_field phi
    phi_orderOf_odd S
  · simpa only [S, GroupExtension.ofNormalSubgroupCoordinates_range_inl]
      using hcentral
  · intro x
    rw [hsq x]
    rfl

end XiLengthTwoTypeAData

/-- Every Peterfalvi type-A model is an inclusive Higman ξ-length-two
type-A model. -/
theorem isXiLengthTwoTypeA_of_isTypeA
    {P : Type uP} [Group P]
    (h : IsTypeA.{uP, uF} P) :
    IsXiLengthTwoTypeA.{uP, uF} P := by
  obtain ⟨d⟩ := h
  exact ⟨XiLengthTwoTypeAData.ofTypeAData d⟩

/-- The raw square equivalence for a homocyclic commutative group of
exponent four. The unreduced final-layer index keeps elaboration cheap. -/
noncomputable def homocyclicFourSquareEquivRaw
    {A ι : Type*} [CommGroup A] [Finite A]
    (ε : A ≃* (ι → Multiplicative (ZMod (2 ^ 2)))) :
    (A ⧸ Agemo A 2 1) ≃* Agemo A 2 (2 - 1) :=
  actualQuotientEquivZeroLayer.trans
    (agemoSuccQuotientEquivLast ε (s := 0) (by omega))

/-- Squaring identifies the quotient by the squares with the subgroup of
squares in a homocyclic commutative group of exponent four. -/
noncomputable def homocyclicFourSquareEquiv
    {A ι : Type*} [CommGroup A] [Finite A]
    (ε : A ≃* (ι → Multiplicative (ZMod (2 ^ 2)))) :
    (A ⧸ Agemo A 2 1) ≃* Agemo A 2 1 := by
  simpa only [Nat.reduceSub] using homocyclicFourSquareEquivRaw ε

@[simp] theorem homocyclicFourSquareEquiv_mk
    {A ι : Type*} [CommGroup A] [Finite A]
    (ε : A ≃* (ι → Multiplicative (ZMod (2 ^ 2)))) (x : A) :
    ((homocyclicFourSquareEquiv ε (QuotientGroup.mk x) : Agemo A 2 1) : A) =
      x ^ 2 := by
  rfl

/-- For a homocyclic commutative group of exponent four, the canonical square
equivalence intertwines every automorphism action. -/
theorem homocyclicFourSquareEquiv_equivariant
    {A X ι : Type*} [CommGroup A] [Group X] [Finite A]
    (phi : X →* MulAut A)
    (ε : A ≃* (ι → Multiplicative (ZMod (2 ^ 2))))
    (g : X) (q : A ⧸ Agemo A 2 1) :
    homocyclicFourSquareEquiv ε
        ((IsAInvariant.of_characteristic phi).quotientMulAutHom g q) =
      agemoRestrictAction phi 1 g (homocyclicFourSquareEquiv ε q) := by
  refine QuotientGroup.induction_on q ?_
  intro a
  apply Subtype.ext
  change (phi g a) ^ 2 = phi g (a ^ 2)
  exact (map_pow (phi g) a 2).symm

/-- The quotient coordinate forced by a prescribed additive coordinate on
the square subgroup.  Frobenius inverse is the normalization for which the
square formula is `beta ↦ beta^2`. -/
noncomputable def homocyclicFourQuotientCoordinate
    {A ι : Type*} [CommGroup A] [Finite A]
    {F : Type uF} [Field F] [Finite F] [CharP F 2]
    (ε : A ≃* (ι → Multiplicative (ZMod (2 ^ 2))))
    (kernelCoord : Additive (Agemo A 2 1) ≃+ F) :
    Additive (A ⧸ Agemo A 2 1) ≃+ F :=
  (homocyclicFourSquareEquiv ε).toAdditive.trans kernelCoord |>.trans
    (frobeniusEquiv F 2).symm.toAddEquiv

/-- If an actor element is scalar `nu` in the prescribed kernel coordinate,
it is scalar `Frob⁻¹(nu)` in the forced quotient coordinate. -/
theorem homocyclicFourQuotientCoordinate_generator_compatible
    {A X ι : Type*} [CommGroup A] [Group X] [Finite A]
    {F : Type uF} [Field F] [Finite F] [CharP F 2]
    (phi : X →* MulAut A)
    (ε : A ≃* (ι → Multiplicative (ZMod (2 ^ 2))))
    (kernelCoord : Additive (Agemo A 2 1) ≃+ F)
    (g : X) (nu : F)
    (hkernel : ∀ z : Additive (Agemo A 2 1),
      kernelCoord (Additive.ofMul (agemoRestrictAction phi 1 g z.toMul)) =
        nu * kernelCoord z)
    (q : Additive (A ⧸ Agemo A 2 1)) :
    homocyclicFourQuotientCoordinate ε kernelCoord
        (Additive.ofMul
          ((IsAInvariant.of_characteristic phi).quotientMulAutHom g q.toMul)) =
      (frobeniusEquiv F 2).symm nu *
        homocyclicFourQuotientCoordinate ε kernelCoord q := by
  change (frobeniusEquiv F 2).symm
      (kernelCoord (Additive.ofMul
        (homocyclicFourSquareEquiv ε
          ((IsAInvariant.of_characteristic phi).quotientMulAutHom g q.toMul)))) = _
  rw [homocyclicFourSquareEquiv_equivariant]
  have hk := hkernel
    (Additive.ofMul (homocyclicFourSquareEquiv ε q.toMul))
  simp only [toMul_ofMul] at hk
  rw [hk]
  exact map_mul (frobeniusEquiv F 2).symm nu
    (kernelCoord
      (Additive.ofMul (homocyclicFourSquareEquiv ε q.toMul)))

/-- A homocyclic commutative group of exponent four is Higman's inclusive
model A(n, 1), with actual finite-field square coordinates. -/
noncomputable def xiLengthTwoTypeAData_of_homocyclic_four
    {A : Type uP} {ι : Type*} [CommGroup A] [Finite A]
    (ε : A ≃* (ι → Multiplicative (ZMod (2 ^ 2))))
    (hNtop : Agemo A 2 1 ≠ ⊤) :
    XiLengthTwoTypeAData.{uP, 0} A := by
  let N : Subgroup A := Agemo A 2 1
  letI : N.Normal := inferInstance
  letI : Nontrivial (A ⧸ N) :=
    QuotientGroup.nontrivial_iff.mpr (by simpa [N] using hNtop)
  let n := Module.finrank (ZMod 2) (Additive (A ⧸ N))
  have hn : 0 < n := Module.finrank_pos
  let F := GaloisField 2 n
  let coord : Additive (A ⧸ N) ≃ₗ[ZMod 2] F :=
    LinearEquiv.ofFinrankEq _ _ (by
      simpa [F, n] using (GaloisField.finrank 2 hn.ne').symm)
  let squareEquiv : (A ⧸ N) ≃* N := by
    simpa [N] using homocyclicFourSquareEquiv ε
  let kernelAdd : Additive N ≃+ F :=
    squareEquiv.toAdditive.symm.trans coord.toAddEquiv
  let quotientAdd : Additive (A ⧸ N) ≃+ F :=
    coord.toAddEquiv.trans (frobeniusEquiv F 2).symm.toAddEquiv
  let kernelMul : N ≃* Multiplicative F :=
    AddEquiv.toMultiplicativeRight kernelAdd
  let left : Multiplicative F ≃* N := kernelMul.symm
  let right : (A ⧸ N) ≃* Multiplicative F :=
    AddEquiv.toMultiplicativeRight quotientAdd
  refine XiLengthTwoTypeAData.ofScaledSquareCoordinates
    n hn (GaloisField.card 2 n hn.ne') (1 : RingAut F) (by simp)
    N left right ?_ (1 : F) one_ne_zero ?_
  · rw [CommGroup.center_eq_top]
    exact le_top
  · intro a
    simp only [one_mul]
    rw [← homocyclicFourSquareEquiv_mk ε a]
    apply congrArg Subtype.val
    apply kernelMul.injective
    simp only [kernelMul, left, MulEquiv.apply_symm_apply]
    apply Multiplicative.ofAdd.injective
    change coord
        (squareEquiv.toAdditive.symm
          (squareEquiv.toAdditive
            (Additive.ofMul (QuotientGroup.mk' N a)))) =
      (frobeniusEquiv F 2).symm
          (coord (Additive.ofMul (QuotientGroup.mk' N a))) *
        (frobeniusEquiv F 2).symm
          (coord (Additive.ofMul (QuotientGroup.mk' N a)))
    rw [squareEquiv.toAdditive.symm_apply_apply]
    rw [← pow_two, frobeniusEquiv_symm_pow_p]

/-- Build the abelian `A(n,1)` model from a prescribed coordinate on its
square subgroup, instead of an actor-blind `LinearEquiv.ofFinrankEq`. -/
noncomputable def xiLengthTwoTypeAData_of_homocyclic_four_prescribedKernel
    {A : Type uP} {ι : Type*} [CommGroup A] [Finite A]
    {F : Type uF} [Field F] [Finite F] [CharP F 2]
    (ε : A ≃* (ι → Multiplicative (ZMod (2 ^ 2))))
    (_hNtop : Agemo A 2 1 ≠ ⊤)
    (parameter : ℕ) (parameter_pos : 0 < parameter)
    (card_field : Nat.card F = 2 ^ parameter)
    (kernelCoord : Additive (Agemo A 2 1) ≃+ F) :
    XiLengthTwoTypeAData.{uP, uF} A := by
  let N : Subgroup A := Agemo A 2 1
  letI : N.Normal := inferInstance
  letI : Nontrivial (A ⧸ N) :=
    QuotientGroup.nontrivial_iff.mpr (by simpa [N] using _hNtop)
  let squareEquiv : (A ⧸ N) ≃* N := by
    simpa [N] using homocyclicFourSquareEquiv ε
  let quotientAdd : Additive (A ⧸ N) ≃+ F :=
    squareEquiv.toAdditive.trans kernelCoord |>.trans
      (frobeniusEquiv F 2).symm.toAddEquiv
  let kernelMul : N ≃* Multiplicative F :=
    AddEquiv.toMultiplicativeRight kernelCoord
  let left : Multiplicative F ≃* N := kernelMul.symm
  let right : (A ⧸ N) ≃* Multiplicative F :=
    AddEquiv.toMultiplicativeRight quotientAdd
  refine XiLengthTwoTypeAData.ofScaledSquareCoordinates
    parameter parameter_pos card_field (1 : RingAut F) (by simp)
    N left right ?_ (1 : F) one_ne_zero ?_
  · rw [CommGroup.center_eq_top]
    exact le_top
  · intro a
    simp only [one_mul]
    rw [← homocyclicFourSquareEquiv_mk ε a]
    apply congrArg Subtype.val
    apply kernelMul.injective
    simp only [kernelMul, left, MulEquiv.apply_symm_apply]
    apply Multiplicative.ofAdd.injective
    change kernelCoord
        (squareEquiv.toAdditive
          (Additive.ofMul (QuotientGroup.mk' N a))) =
      (frobeniusEquiv F 2).symm
          (kernelCoord (squareEquiv.toAdditive
            (Additive.ofMul (QuotientGroup.mk' N a)))) *
        (frobeniusEquiv F 2).symm
          (kernelCoord (squareEquiv.toAdditive
            (Additive.ofMul (QuotientGroup.mk' N a))))
    rw [← pow_two, frobeniusEquiv_symm_pow_p]

/-- In an abelian exponent-four factor, the square subgroup is exactly the
intersection with the ambient Frattini subgroup. -/
theorem agemo_one_eq_frattini_subgroupOf_of_homocyclic_four
    {P : Type uP} [Group P]
    {S : Subgroup P} {ι : Type*} [Finite P]
    (hcommS : IsMulCommutative S)
    (ε : S ≃* (ι → Multiplicative (ZMod (2 ^ 2))))
    (hinvPhi : involutions P ⊆ frattini P)
    (hEA : IsElementaryAbelian 2 ↑(frattini P)) :
    Agemo S 2 1 = (frattini P).subgroupOf S := by
  letI : CommGroup S :=
    { (inferInstance : Group S) with mul_comm := hcommS.is_comm.comm }
  ext z
  change z ∈ Agemo S 2 1 ↔ (z : P) ∈ frattini P
  have hsq : z ^ 2 = 1 ↔ z ∈ Agemo S 2 1 := by
    simpa only [Nat.reduceSub] using
      (sq_eq_one_iff_mem_lastAgemoLayer (A := S) (ι := ι) (e := 2)
        ε (by omega) (x := z))
  rw [← hsq]
  constructor
  · intro hz
    by_cases hzOne : (z : P) = 1
    · simp [hzOne]
    · apply hinvPhi
      exact ⟨by simpa using congrArg Subtype.val hz, hzOne⟩
  · intro hz
    apply Subtype.ext
    simpa using congrArg Subtype.val (hEA.pow_eq_one ⟨(z : P), hz⟩)

/-- Identity-on-underlying-values equivalence between the square subgroup of
the factor and the ambient Frattini group. -/
def homocyclicFourSquareSubgroupEquivFrattini
    {P : Type uP} [Group P] {S : Subgroup P}
    (hPhiS : frattini P ≤ S)
    (hN : Agemo S 2 1 = (frattini P).subgroupOf S) :
    Agemo S 2 1 ≃* frattini P where
  toFun z := ⟨((z : S) : P), by
    have hz : (z : S) ∈ (frattini P).subgroupOf S := by
      rw [← hN]
      exact z.2
    exact hz⟩
  invFun z := ⟨⟨z.1, hPhiS z.2⟩, by
    rw [hN]
    exact z.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- The identity-on-values equivalence intertwines the restricted factor
action and the ambient action on `Φ(P)`. -/
theorem homocyclicFourSquareSubgroupEquivFrattini_equivariant
    {P : Type uP} [Group P]
    {Y : Subgroup (MulAut P)} {S : Subgroup P}
    (hSinv : IsAInvariant Y.subtype S)
    (hPhiS : frattini P ≤ S)
    (hN : Agemo S 2 1 = (frattini P).subgroupOf S)
    (c : Y) (z : Agemo S 2 1) :
    homocyclicFourSquareSubgroupEquivFrattini hPhiS hN
        ((IsAInvariant.of_characteristic hSinv.restrict).restrict c z) =
      (IsAInvariant.of_characteristic Y.subtype).restrict c
        (homocyclicFourSquareSubgroupEquivFrattini hPhiS hN z) := by
  rfl

/-- Transport an ambient Frattini additive coordinate to the factor's square
subgroup. -/
noncomputable def homocyclicFourPrescribedKernelCoordinate
    {P : Type uP} [Group P] {S : Subgroup P}
    {F : Type uF} [AddCommGroup F]
    (hPhiS : frattini P ≤ S)
    (hN : Agemo S 2 1 = (frattini P).subgroupOf S)
    (e : Additive (frattini P) ≃+ F) :
    Additive (Agemo S 2 1) ≃+ F :=
  (homocyclicFourSquareSubgroupEquivFrattini hPhiS hN).toAdditive.trans e

/-- Generator compatibility of the kernel coordinate transported from the
ambient Frattini Singer coordinate. -/
theorem homocyclicFourPrescribedKernelCoordinate_generator_compatible
    {P : Type uP} [Group P]
    {Y : Subgroup (MulAut P)} {S : Subgroup P}
    {F : Type uF} [Field F]
    (hSinv : IsAInvariant Y.subtype S)
    (hPhiS : frattini P ≤ S)
    (hN : Agemo S 2 1 = (frattini P).subgroupOf S)
    (e : Additive (frattini P) ≃+ F)
    (c : Y) (nu : F)
    (he : ∀ v : Additive (frattini P),
      e (Additive.ofMul
        ((IsAInvariant.of_characteristic Y.subtype).restrict c v.toMul)) =
          nu * e v)
    (z : Additive (Agemo S 2 1)) :
    homocyclicFourPrescribedKernelCoordinate hPhiS hN e
        (Additive.ofMul
          ((IsAInvariant.of_characteristic hSinv.restrict).restrict c z.toMul)) =
      nu * homocyclicFourPrescribedKernelCoordinate hPhiS hN e z := by
  change e (Additive.ofMul
      (homocyclicFourSquareSubgroupEquivFrattini hPhiS hN
        ((IsAInvariant.of_characteristic hSinv.restrict).restrict c z.toMul))) =
    nu * e (Additive.ofMul
      (homocyclicFourSquareSubgroupEquivFrattini hPhiS hN z.toMul))
  rw [homocyclicFourSquareSubgroupEquivFrattini_equivariant]
  have h := he (Additive.ofMul
    (homocyclicFourSquareSubgroupEquivFrattini hPhiS hN z.toMul))
  simpa only [toMul_ofMul] using h

/-- The faithful range of an invariant subgroup restriction is again a
cyclic actor transitive on that subgroup's involutions. -/
theorem restricted_range_isXiActor
    {P : Type uP} [Group P]
    {Y : Subgroup (MulAut P)}
    (hxi : IsXiActor Y)
    {S : Subgroup P}
    (hSinv : IsAInvariant Y.subtype S) :
    IsXiActor hSinv.restrict.range := by
  refine ⟨?_, ?_⟩
  · letI : IsCyclic Y := hxi.cyclic
    exact isCyclic_of_surjective hSinv.restrict.rangeRestrict
      hSinv.restrict.rangeRestrict_surjective
  · intro x hx y hy
    have hxP : (x : P) ∈ involutions P := by
      refine ⟨congrArg Subtype.val hx.1, ?_⟩
      intro hx1
      exact hx.2 (Subtype.ext hx1)
    have hyP : (y : P) ∈ involutions P := by
      refine ⟨congrArg Subtype.val hy.1, ?_⟩
      intro hy1
      exact hy.2 (Subtype.ext hy1)
    obtain ⟨a, ha⟩ := hxi.transitive (x : P) hxP (y : P) hyP
    refine ⟨hSinv.restrict.rangeRestrict a, ?_⟩
    exact Subtype.ext ha

/-- A prescribed ambient generator remains a generator after passing to the
faithful range of an invariant-subgroup restriction. -/
theorem forall_mem_zpowers_restrictedRange_generator
    {P : Type uP} [Group P]
    {Y : Subgroup (MulAut P)}
    {S : Subgroup P}
    (hSinv : IsAInvariant Y.subtype S)
    (c : Y) (hcgen : ∀ g : Y, g ∈ Subgroup.zpowers c) :
    ∀ g : hSinv.restrict.range,
      g ∈ Subgroup.zpowers (hSinv.restrict.rangeRestrict c) := by
  intro g
  obtain ⟨y, rfl⟩ := hSinv.restrict.rangeRestrict_surjective g
  rw [← MonoidHom.map_zpowers hSinv.restrict.rangeRestrict c]
  exact ⟨y, hcgen y, rfl⟩

/-- If a subgroup contains every ambient involution, it has exactly the
same number of involutions as the ambient group. -/
theorem involutions_ncard_subgroup_eq_of_subset
    {P : Type uP} [Group P]
    (S : Subgroup P)
    (hinvS : involutions P ⊆ S) :
    (involutions S).ncard = (involutions P).ncard := by
  let f : ↑(involutions S) → ↑(involutions P) := fun x =>
    ⟨((x.1 : S) : P), by
      refine ⟨congrArg Subtype.val x.2.1, ?_⟩
      intro hx1
      exact x.2.2 (Subtype.ext hx1)⟩
  have hf_injective : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    have hxyP := congrArg
      (fun z : ↑(involutions P) => (z : P)) hxy
    simpa [f] using hxyP
  have hf_surjective : Function.Surjective f := by
    intro z
    let s : S := ⟨z.1, hinvS z.2⟩
    have hs : s ∈ involutions S := by
      refine ⟨?_, ?_⟩
      · apply Subtype.ext
        exact z.2.1
      · intro hs1
        apply z.2.2
        exact congrArg Subtype.val hs1
    refine ⟨⟨s, hs⟩, ?_⟩
    apply Subtype.ext
    rfl
  calc
    (involutions S).ncard = Nat.card ↑(involutions S) :=
      (Nat.card_coe_set_eq (involutions S)).symm
    _ = Nat.card ↑(involutions P) :=
      Nat.card_congr (Equiv.ofBijective f ⟨hf_injective, hf_surjective⟩)
    _ = (involutions P).ncard := Nat.card_coe_set_eq (involutions P)

/-- Two distinct ambient involutions give two distinct involutions in any
subgroup which contains every ambient involution. -/
theorem exists_distinct_involutions_subgroup_of_subset
    {P : Type uP} [Group P]
    {S : Subgroup P}
    (hinvS : involutions P ⊆ S)
    (hmulti : ∃ x y : P,
      x ∈ involutions P ∧ y ∈ involutions P ∧ x ≠ y) :
    ∃ x y : S,
      x ∈ involutions S ∧ y ∈ involutions S ∧ x ≠ y := by
  obtain ⟨x, y, hx, hy, hxy⟩ := hmulti
  let xs : S := ⟨x, hinvS hx⟩
  let ys : S := ⟨y, hinvS hy⟩
  refine ⟨xs, ys, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · exact Subtype.ext hx.1
    · intro hxs
      exact hx.2 (congrArg Subtype.val hxs)
  · refine ⟨?_, ?_⟩
    · exact Subtype.ext hy.1
    · intro hys
      exact hy.2 (congrArg Subtype.val hys)
  · intro hxys
    exact hxy (congrArg Subtype.val hxys)

/-- Higman's prime-support condition descends from the original actor to
the faithful range of its restriction. -/
theorem restricted_range_primeSupport
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    {S : Subgroup P}
    (hSinv : IsAInvariant Y.subtype S)
    (hinvS : involutions P ⊆ S)
    (hprime : ∀ p : ℕ, p.Prime → p ∣ Nat.card Y →
      p ∣ (involutions P).ncard) :
    ∀ p : ℕ, p.Prime → p ∣ Nat.card hSinv.restrict.range →
      p ∣ (involutions S).ncard := by
  intro p hp hpRange
  rw [involutions_ncard_subgroup_eq_of_subset S hinvS]
  exact hprime p hp
    (hpRange.trans (Subgroup.card_range_dvd hSinv.restrict))

set_option maxHeartbeats 800000 in
-- The contradiction compares two Agemo layers through the invariant lattice.
/-- A commutative 2-group with xi-length two and more than one involution is
homocyclic of exponent four. This is Higman's abelian A(n, 1) branch. -/
theorem exists_homocyclic_four_of_commutative_xiLengthTwo
    {A : Type uP} [CommGroup A] [Finite A]
    {Y : Subgroup (MulAut A)}
    (hA : IsPGroup 2 A)
    (hxi : IsXiActor Y)
    (hlen : HasXiLengthTwo Y.subtype)
    (hmulti : ∃ x y : A,
      x ∈ involutions A ∧ y ∈ involutions A ∧ x ≠ y) :
    ∃ (ι : Type) (_ : Fintype ι),
      Nonempty (A ≃* (ι → Multiplicative (ZMod 4))) := by
  obtain ⟨ι, hι, e, he, ⟨ε⟩, hclass⟩ :=
    exists_homocyclic_and_invariant_eq_agemo
      hA Y.subtype hxi.transitive
  obtain ⟨M, hbotM, hMtop⟩ := hlen.exists_middle
  obtain ⟨s, hse, hM⟩ := hclass M.1 M.2.2
  have hs0 : s ≠ 0 := by
    intro hs
    subst s
    apply hMtop.ne
    apply Subtype.ext
    change M.1 = (⊤ : Subgroup A)
    simpa [agemo_zero_eq_top] using hM
  have hsne : s ≠ e := by
    intro hs
    subst s
    apply hbotM.ne'
    apply Subtype.ext
    change M.1 = (⊥ : Subgroup A)
    simpa [agemo_two_eq_bot_of_equiv_pi_zmod ε] using hM
  have he2 : 2 ≤ e := by omega
  have he_le : e ≤ 2 := by
    by_contra hnot
    have he3 : 3 ≤ e := by omega
    obtain ⟨x, _, hx, _, _⟩ := hmulti
    have hxlast : x ∈ Agemo A 2 (e - 1) :=
      (sq_eq_one_iff_mem_lastAgemoLayer ε he).mp hx.1
    have hxone : x ∈ Agemo A 2 1 :=
      (Agemo.anti (by omega : 1 ≤ e - 1)) hxlast
    have hxtwo : x ∈ Agemo A 2 2 :=
      (Agemo.anti (by omega : 2 ≤ e - 1)) hxlast
    have hOneNeBot : Agemo A 2 1 ≠ (⊥ : Subgroup A) := by
      intro hbot
      have := hxone
      rw [hbot] at this
      exact hx.2 (Subgroup.mem_bot.mp this)
    have hTwoNeBot : Agemo A 2 2 ≠ (⊥ : Subgroup A) := by
      intro hbot
      have := hxtwo
      rw [hbot] at this
      exact hx.2 (Subgroup.mem_bot.mp this)
    letI : Nontrivial (Agemo A 2 1) :=
      (Subgroup.nontrivial_iff_ne_bot (Agemo A 2 1)).mpr hOneNeBot
    letI : Nontrivial A :=
      (Agemo A 2 1).subtype_injective.nontrivial
    have hPhiNeTop : frattini A ≠ (⊤ : Subgroup A) := by
      obtain ⟨N, hN, _⟩ :=
        (IsCoatomic.eq_top_or_exists_le_coatom (⊥ : Subgroup A)).resolve_left
          bot_lt_top.ne
      exact fun htop => hN.1
        (le_antisymm le_top (htop ▸ frattini_le_coatom hN))
    have hOneNeTop : Agemo A 2 1 ≠ (⊤ : Subgroup A) := by
      rw [← NormalInvariantCover.frattini_eq_agemo_one hA]
      exact hPhiNeTop
    have hTwoNeTop : Agemo A 2 2 ≠ (⊤ : Subgroup A) := by
      intro htop
      apply hOneNeTop
      apply top_unique
      rw [← htop]
      exact Agemo.anti (by omega : 1 ≤ 2)
    let U : NormalInvariantSubgroup Y.subtype :=
      ⟨Agemo A 2 1, ⟨inferInstance,
        IsAInvariant.of_characteristic Y.subtype⟩⟩
    let V : NormalInvariantSubgroup Y.subtype :=
      ⟨Agemo A 2 2, ⟨inferInstance,
        IsAInvariant.of_characteristic Y.subtype⟩⟩
    have hUneBot : U ≠ normalInvariantBot Y.subtype := by
      intro h
      exact hOneNeBot (congrArg Subtype.val h)
    have hUneTop : U ≠ normalInvariantTop Y.subtype := by
      intro h
      exact hOneNeTop (congrArg Subtype.val h)
    have hVneBot : V ≠ normalInvariantBot Y.subtype := by
      intro h
      exact hTwoNeBot (congrArg Subtype.val h)
    have hVneTop : V ≠ normalInvariantTop Y.subtype := by
      intro h
      exact hTwoNeTop (congrArg Subtype.val h)
    have hUV : U = V :=
      hlen.eq_of_ne_bot_of_ne_top hA hxi.transitive
        hUneBot hUneTop hVneBot hVneTop
    have hOneTwo : Agemo A 2 1 = Agemo A 2 2 :=
      congrArg Subtype.val hUV
    let B := Agemo A 2 1
    letI : Nontrivial B :=
      (Subgroup.nontrivial_iff_ne_bot B).mpr hOneNeBot
    have hBFratNeTop : frattini B ≠ (⊤ : Subgroup B) := by
      obtain ⟨N, hN, _⟩ :=
        (IsCoatomic.eq_top_or_exists_le_coatom (⊥ : Subgroup B)).resolve_left
          bot_lt_top.ne
      exact fun htop => hN.1
        (le_antisymm le_top (htop ▸ frattini_le_coatom hN))
    apply hBFratNeTop
    rw [NormalInvariantCover.frattini_eq_agemo_one (hA.to_subgroup B)]
    rw [← agemo_succ_subgroupOf_eq_agemo_one (A := A) (p := 2) (s := 1)]
    exact Subgroup.subgroupOf_eq_top.mpr (by simpa [B] using hOneTwo.le)
  have heq : e = 2 := le_antisymm he_le he2
  subst e
  simpa using ⟨ι, ⟨hι⟩, ⟨ε⟩⟩

/-- A noncommutative proper invariant subgroup strictly above `Φ(P)` is
of Peterfalvi type A, by applying Higman's Lemma 11 to the faithful
restricted actor. -/
theorem isTypeA_invariant_subgroup_of_xiLengthThree
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hncomm : ¬ IsMulCommutative P)
    (hmulti : ∃ x y : P,
      x ∈ involutions P ∧ y ∈ involutions P ∧ x ≠ y)
    (hxi : IsXiActor Y)
    (hlen : HasXiLengthThree Y.subtype)
    (hprime : ∀ p : ℕ, p.Prime → p ∣ Nat.card Y →
      p ∣ (involutions P).ncard)
    {S : Subgroup P}
    (hSinv : IsAInvariant Y.subtype S)
    (hPhiS : frattini P < S)
    (hStop : S < (⊤ : Subgroup P))
    (hncommS : ¬ IsMulCommutative S) :
    IsTypeA.{uP, 0} S := by
  have hSneBot : S ≠ (⊥ : Subgroup P) :=
    ne_of_gt (lt_of_le_of_lt bot_le hPhiS)
  have hinvS : involutions P ⊆ S :=
    involutions_subset_of_nontrivial_invariant
      hP Y hxi.transitive hSinv hSneBot
  have hEA : IsElementaryAbelian 2 ↑(frattini P) :=
    frattini_isElementaryAbelian_of_xiLengthThree
      hP hncomm hmulti hxi hlen hprime
  have hxiS : IsXiActor hSinv.restrict.range :=
    restricted_range_isXiActor hxi hSinv
  have hlenS : HasXiLengthTwo hSinv.restrict.range.subtype :=
    restricted_range_hasXiLengthTwo_of_xiLengthThree
      hP hncomm hxi hlen hEA hSinv hPhiS hStop
  have hmultiS : ∃ x y : S,
      x ∈ involutions S ∧ y ∈ involutions S ∧ x ≠ y :=
    exists_distinct_involutions_subgroup_of_subset hinvS hmulti
  have hprimeS : ∀ p : ℕ, p.Prime →
      p ∣ Nat.card hSinv.restrict.range →
        p ∣ (involutions S).ncard :=
    restricted_range_primeSupport hSinv hinvS hprime
  exact higmanLemmaEleven (hP.to_subgroup S) hncommS hmultiS
    hxiS hlenS hprimeS

/-- The noncommutative branch of a lifted ξ-length-two factor has the
inclusive source-facing `A(n, φ)` model. -/
theorem isXiLengthTwoTypeA_invariant_subgroup_of_xiLengthThree_of_noncommutative
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hncomm : ¬ IsMulCommutative P)
    (hmulti : ∃ x y : P,
      x ∈ involutions P ∧ y ∈ involutions P ∧ x ≠ y)
    (hxi : IsXiActor Y)
    (hlen : HasXiLengthThree Y.subtype)
    (hprime : ∀ p : ℕ, p.Prime → p ∣ Nat.card Y →
      p ∣ (involutions P).ncard)
    {S : Subgroup P}
    (hSinv : IsAInvariant Y.subtype S)
    (hPhiS : frattini P < S)
    (hStop : S < (⊤ : Subgroup P))
    (hncommS : ¬ IsMulCommutative S) :
    IsXiLengthTwoTypeA.{uP, 0} S :=
  isXiLengthTwoTypeA_of_isTypeA
    (isTypeA_invariant_subgroup_of_xiLengthThree
      hP hncomm hmulti hxi hlen hprime hSinv hPhiS hStop hncommS)

/-- The commutative branch of a lifted xi-length-two factor is Higman's
abelian model A(n, 1), not Peterfalvi's noncommutative TypeAData. -/
theorem isXiLengthTwoTypeA_invariant_subgroup_of_xiLengthThree_of_commutative
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hncomm : ¬ IsMulCommutative P)
    (hmulti : ∃ x y : P,
      x ∈ involutions P ∧ y ∈ involutions P ∧ x ≠ y)
    (hxi : IsXiActor Y)
    (hlen : HasXiLengthThree Y.subtype)
    (hprime : ∀ p : ℕ, p.Prime → p ∣ Nat.card Y →
      p ∣ (involutions P).ncard)
    {S : Subgroup P}
    (hSinv : IsAInvariant Y.subtype S)
    (hPhiS : frattini P < S)
    (hStop : S < (⊤ : Subgroup P))
    (hcommS : IsMulCommutative S) :
    IsXiLengthTwoTypeA.{uP, 0} S := by
  letI : CommGroup S :=
    { (inferInstance : Group S) with mul_comm := hcommS.is_comm.comm }
  have hSneBot : S ≠ (⊥ : Subgroup P) :=
    ne_of_gt (lt_of_le_of_lt bot_le hPhiS)
  letI : Nontrivial S :=
    (Subgroup.nontrivial_iff_ne_bot S).mpr hSneBot
  have hinvS : involutions P ⊆ S :=
    involutions_subset_of_nontrivial_invariant
      hP Y hxi.transitive hSinv hSneBot
  have hEA : IsElementaryAbelian 2 ↑(frattini P) :=
    frattini_isElementaryAbelian_of_xiLengthThree
      hP hncomm hmulti hxi hlen hprime
  have hxiS : IsXiActor hSinv.restrict.range :=
    restricted_range_isXiActor hxi hSinv
  have hlenS : HasXiLengthTwo hSinv.restrict.range.subtype :=
    restricted_range_hasXiLengthTwo_of_xiLengthThree
      hP hncomm hxi hlen hEA hSinv hPhiS hStop
  have hmultiS : ∃ x y : S,
      x ∈ involutions S ∧ y ∈ involutions S ∧ x ≠ y :=
    exists_distinct_involutions_subgroup_of_subset hinvS hmulti
  obtain ⟨ι, _, ⟨ε⟩⟩ :=
    exists_homocyclic_four_of_commutative_xiLengthTwo
      (hP.to_subgroup S) hxiS hlenS hmultiS
  have hFrattiniNeTop : frattini S ≠ (⊤ : Subgroup S) := by
    obtain ⟨M, hM, _⟩ :=
      (IsCoatomic.eq_top_or_exists_le_coatom (⊥ : Subgroup S)).resolve_left
        bot_lt_top.ne
    exact fun htop => hM.1
      (le_antisymm le_top (htop ▸ frattini_le_coatom hM))
  have hAgemoNeTop : Agemo S 2 1 ≠ (⊤ : Subgroup S) := by
    rw [← NormalInvariantCover.frattini_eq_agemo_one (hP.to_subgroup S)]
    exact hFrattiniNeTop
  have ε' : S ≃* (ι → Multiplicative (ZMod (2 ^ 2))) := by
    simpa using ε
  exact ⟨xiLengthTwoTypeAData_of_homocyclic_four ε' hAgemoNeTop⟩

/-- Every proper invariant factor strictly above the ambient Frattini
subgroup has Higman's inclusive A(n, phi) model. -/
theorem isXiLengthTwoTypeA_invariant_subgroup_of_xiLengthThree
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hncomm : ¬ IsMulCommutative P)
    (hmulti : ∃ x y : P,
      x ∈ involutions P ∧ y ∈ involutions P ∧ x ≠ y)
    (hxi : IsXiActor Y)
    (hlen : HasXiLengthThree Y.subtype)
    (hprime : ∀ p : ℕ, p.Prime → p ∣ Nat.card Y →
      p ∣ (involutions P).ncard)
    {S : Subgroup P}
    (hSinv : IsAInvariant Y.subtype S)
    (hPhiS : frattini P < S)
    (hStop : S < (⊤ : Subgroup P)) :
    IsXiLengthTwoTypeA.{uP, 0} S := by
  by_cases hcommS : IsMulCommutative S
  · exact
      isXiLengthTwoTypeA_invariant_subgroup_of_xiLengthThree_of_commutative
        hP hncomm hmulti hxi hlen hprime hSinv hPhiS hStop hcommS
  · exact
      isXiLengthTwoTypeA_invariant_subgroup_of_xiLengthThree_of_noncommutative
        hP hncomm hmulti hxi hlen hprime hSinv hPhiS hStop hcommS

/-- A group equivalence restricts to an equivalence between the sets of
nonidentity involutions. -/
def mulEquivInvolutions
    {P : Type uP} {Q : Type uQ} [Group P] [Group Q]
    (e : P ≃* Q) : ↑(involutions P) ≃ ↑(involutions Q) where
  toFun x :=
    ⟨e x.1, by
      refine ⟨?_, ?_⟩
      · simpa only [map_pow, map_one] using congrArg e x.2.1
      · intro hx
        apply x.2.2
        exact e.injective (by simpa using hx)⟩
  invFun x :=
    ⟨e.symm x.1, by
      refine ⟨?_, ?_⟩
      · simpa only [map_pow, map_one] using congrArg e.symm x.2.1
      · intro hx
        apply x.2.2
        exact e.symm.injective (by simpa using hx)⟩
  left_inv x := by simp
  right_inv x := by simp

section TypeAModelInvolutions

variable {F : Type uF} [Field F] [Finite F] [CharP F 2]

local instance : Algebra (ZMod 2) F := ZMod.algebra F 2

/-- In the concrete model A(n, phi), the nonidentity involutions are exactly
the elements with zero quotient coordinate and nonzero central coordinate. -/
theorem typeAModel_mem_involutions_iff
    (phi : RingAut F) (x : TypeAModel phi) :
    x ∈ involutions (TypeAModel phi) ↔
      x.quotient = 0 ∧ x.central ≠ 0 := by
  constructor
  · intro hx
    have hinl :
        (QuadraticExtension.extension
          (typeAQuadraticMap phi)
          (Module.finBasis (ZMod 2) F)).inl
            (Multiplicative.ofAdd (x.quotient * phi x.quotient)) = 1 :=
      (TypeAModel.sq_eq_inl_quadraticMap phi x).symm.trans hx.1
    have hmul :
        Multiplicative.ofAdd (x.quotient * phi x.quotient) = 1 := by
      apply (QuadraticExtension.extension
        (typeAQuadraticMap phi)
        (Module.finBasis (ZMod 2) F)).inl_injective
      simpa using hinl
    have hprod : x.quotient * phi x.quotient = 0 := by
      simpa using congrArg Multiplicative.toAdd hmul
    have hquot : x.quotient = 0 := by
      rcases mul_eq_zero.mp hprod with h | h
      · exact h
      · exact phi.injective (by simpa using h)
    refine ⟨hquot, ?_⟩
    intro hcentral
    apply hx.2
    apply BilinearTwistedProduct.ext
    · simpa using hquot
    · simpa using hcentral
  · rintro ⟨hquot, hcentral⟩
    refine ⟨?_, ?_⟩
    · rw [TypeAModel.sq_eq_inl_quadraticMap]
      simp [hquot]
    · intro hx
      apply hcentral
      simpa using congrArg BilinearTwistedProduct.central hx

/-- The involutions of A(n, phi) are equivalent to the nonzero elements of
its defining field. -/
noncomputable def typeAModelInvolutionsEquivNonzero
    (phi : RingAut F) :
    ↑(involutions (TypeAModel phi)) ≃ {a : F // a ≠ 0} where
  toFun x :=
    ⟨x.1.central, (typeAModel_mem_involutions_iff phi x.1).mp x.2 |>.2⟩
  invFun a :=
    ⟨⟨0, a.1⟩, (typeAModel_mem_involutions_iff phi ⟨0, a.1⟩).mpr
      ⟨rfl, a.2⟩⟩
  left_inv x := by
    apply Subtype.ext
    apply BilinearTwistedProduct.ext
    · exact ((typeAModel_mem_involutions_iff phi x.1).mp x.2 |>.1).symm
    · rfl
  right_inv a := rfl

/-- The concrete model A(n, phi) has one nonidentity involution for each
nonzero element of its defining field. -/
theorem typeAModel_involutions_ncard_eq
    (phi : RingAut F) :
    (involutions (TypeAModel phi)).ncard = Nat.card F - 1 := by
  classical
  letI := Fintype.ofFinite F
  calc
    (involutions (TypeAModel phi)).ncard =
        Nat.card ↑(involutions (TypeAModel phi)) :=
      (Nat.card_coe_set_eq _).symm
    _ = Nat.card {a : F // a ≠ 0} :=
      Nat.card_congr (typeAModelInvolutionsEquivNonzero phi)
    _ = Nat.card F - 1 := by
      simp only [Nat.card_eq_fintype_card]
      rw [Fintype.card_subtype_compl (fun a : F => a = 0)]
      simp

end TypeAModelInvolutions

namespace XiLengthTwoTypeAData

/-- The number of involutions in an inclusive Higman A(n, phi) model is
2^n - 1. -/
theorem involutions_ncard_eq
    {P : Type uP} [Group P]
    (data : XiLengthTwoTypeAData.{uP, uF} P) :
    (involutions P).ncard = 2 ^ data.parameter - 1 := by
  letI : Field data.F := data.fieldF
  letI : Finite data.F := data.finiteF
  letI : CharP data.F 2 := data.charTwoF
  calc
    (involutions P).ncard = Nat.card ↑(involutions P) :=
      (Nat.card_coe_set_eq _).symm
    _ = Nat.card ↑(involutions (TypeAModel data.phi)) :=
      Nat.card_congr (mulEquivInvolutions data.equivModel)
    _ = (involutions (TypeAModel data.phi)).ncard :=
      Nat.card_coe_set_eq _
    _ = Nat.card data.F - 1 :=
      typeAModel_involutions_ncard_eq data.phi
    _ = 2 ^ data.parameter - 1 := by rw [data.card_field]

/-- The number of involutions uniquely determines the field parameter of an
inclusive Higman type-A model. -/
theorem parameter_eq_of_involutions_ncard_eq
    {P : Type uP} {Q : Type uQ} [Group P] [Group Q]
    (dataP : XiLengthTwoTypeAData.{uP, uF} P)
    (dataQ : XiLengthTwoTypeAData.{uQ, uE} Q)
    (hcard : (involutions P).ncard = (involutions Q).ncard) :
    dataP.parameter = dataQ.parameter := by
  apply Nat.pow_right_injective le_rfl
  apply Nat.sub_one_cancel (pow_pos (by omega) dataP.parameter)
    (pow_pos (by omega) dataQ.parameter)
  exact dataP.involutions_ncard_eq.symm.trans
    (hcard.trans dataQ.involutions_ncard_eq)

/-- More than one involution forces Higman's field parameter to be at least
two. -/
theorem parameter_two_le_of_exists_distinct_involutions
    {P : Type uP} [Group P] [Finite P]
    (data : XiLengthTwoTypeAData.{uP, uF} P)
    (hmulti : ∃ x y : P,
      x ∈ involutions P ∧ y ∈ involutions P ∧ x ≠ y) :
    2 ≤ data.parameter := by
  obtain ⟨x, y, hx, hy, hxy⟩ := hmulti
  have hinvTwo : 2 ≤ (involutions P).ncard := by
    calc
      2 = ({x, y} : Set P).ncard := (Set.ncard_pair hxy).symm
      _ ≤ (involutions P).ncard := by
        apply Set.ncard_mono
        intro z hz
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
        rcases hz with rfl | rfl
        · exact hx
        · exact hy
  rw [data.involutions_ncard_eq] at hinvTwo
  by_contra h
  have hpos := data.parameter_pos
  have hparam : data.parameter = 1 := by omega
  rw [hparam] at hinvTwo
  norm_num at hinvTwo

end XiLengthTwoTypeAData

/-- Honest data for the two complementary A(n, phi) factors in Higman's
Lemma 12, including their common parameter and its lower bound. The two field
automorphisms are not asserted to be equal. -/
structure XiLengthThreeTypeAFactorData
    (P : Type uP) [Group P] (Y : Subgroup (MulAut P)) where
  left : Subgroup P
  right : Subgroup P
  left_normal : left.Normal
  left_invariant : IsAInvariant Y.subtype left
  right_normal : right.Normal
  right_invariant : IsAInvariant Y.subtype right
  frattini_lt_left : frattini P < left
  left_lt_top : left < ⊤
  frattini_lt_right : frattini P < right
  right_lt_top : right < ⊤
  inf_eq_frattini : left ⊓ right = frattini P
  sup_eq_top : left ⊔ right = ⊤
  left_model : XiLengthTwoTypeAData.{uP, 0} left
  right_model : XiLengthTwoTypeAData.{uP, 0} right
  parameter_eq : left_model.parameter = right_model.parameter
  parameter_two_le : 2 ≤ left_model.parameter

/-- **Higman Lemma 12 (p. 90), common-parameter factor step.**

The complementary Frattini preimages are actual A(n, theta) and A(n, phi)
models with one common parameter n at least two. -/
theorem xiLengthThreeTypeAFactorData_exists
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hncomm : ¬ IsMulCommutative P)
    (hmulti : ∃ x y : P,
      x ∈ involutions P ∧ y ∈ involutions P ∧ x ≠ y)
    (hxi : IsXiActor Y)
    (hlen : HasXiLengthThree Y.subtype)
    (hprime : ∀ p : ℕ, p.Prime → p ∣ Nat.card Y →
      p ∣ (involutions P).ncard) :
    Nonempty (XiLengthThreeTypeAFactorData P Y) := by
  obtain ⟨X, Z, hXnormal, hXinv, hZnormal, hZinv,
      hPhiX, hXtop, hPhiZ, hZtop, hXbot, hZbot, hXZinf, hXZsup⟩ :=
    exists_complementary_invariant_frattini_preimages_of_xiLengthThree
      hP hncomm hmulti hxi hlen hprime
  obtain ⟨dataX⟩ :=
    isXiLengthTwoTypeA_invariant_subgroup_of_xiLengthThree
      hP hncomm hmulti hxi hlen hprime hXinv hPhiX hXtop
  obtain ⟨dataZ⟩ :=
    isXiLengthTwoTypeA_invariant_subgroup_of_xiLengthThree
      hP hncomm hmulti hxi hlen hprime hZinv hPhiZ hZtop
  have hinvX : involutions P ⊆ X :=
    involutions_subset_of_nontrivial_invariant
      hP Y hxi.transitive hXinv hXbot
  have hinvZ : involutions P ⊆ Z :=
    involutions_subset_of_nontrivial_invariant
      hP Y hxi.transitive hZinv hZbot
  have hcardXZ :
      (involutions X).ncard = (involutions Z).ncard :=
    (involutions_ncard_subgroup_eq_of_subset X hinvX).trans
      (involutions_ncard_subgroup_eq_of_subset Z hinvZ).symm
  have hparam : dataX.parameter = dataZ.parameter :=
    XiLengthTwoTypeAData.parameter_eq_of_involutions_ncard_eq
      dataX dataZ hcardXZ
  have hmultiX : ∃ x y : X,
      x ∈ involutions X ∧ y ∈ involutions X ∧ x ≠ y :=
    exists_distinct_involutions_subgroup_of_subset hinvX hmulti
  have htwo : 2 ≤ dataX.parameter :=
    XiLengthTwoTypeAData.parameter_two_le_of_exists_distinct_involutions
      dataX hmultiX
  exact ⟨
    { left := X
      right := Z
      left_normal := hXnormal
      left_invariant := hXinv
      right_normal := hZnormal
      right_invariant := hZinv
      frattini_lt_left := hPhiX
      left_lt_top := hXtop
      frattini_lt_right := hPhiZ
      right_lt_top := hZtop
      inf_eq_frattini := hXZinf
      sup_eq_top := hXZsup
      left_model := dataX
      right_model := dataZ
      parameter_eq := hparam
      parameter_two_le := htwo }⟩

end OddOrder.Higman.Suzuki2Groups
