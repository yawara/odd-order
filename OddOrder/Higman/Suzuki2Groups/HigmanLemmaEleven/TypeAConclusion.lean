/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaEleven.ProperExtension
import OddOrder.Peterfalvi.Appendices.Suzuki2Groups.Types

/-!
# Higman's Lemma 11: the type-A conclusion

G. Higman, “Suzuki 2-groups,” *Illinois Journal of Mathematics* 7 (1963),
Lemma 11, p. 89.

This leaf converts the two actual lower-central layers into kernel and
quotient coordinates for a central group extension.  It also absorbs the
nonzero scalar in Higman's square formula into the kernel coordinate and
feeds the resulting square map to Peterfalvi's concrete type-A model.
-/

set_option autoImplicit false

open scoped IsMulCommutative
open OddOrder.GroupTheory
open OddOrder.Peterfalvi.Appendices.Suzuki2Groups

namespace OddOrder.Higman.Suzuki2Groups

universe uP uF uK uL

noncomputable section

local instance lowerCentralTermOneNormalForCoordinates
    (P : Type uP) [Group P] :
    (lowerCentralTerm P 1).Normal := by
  dsimp [lowerCentralTerm]
  infer_instance

/-! ## The Frobenius automorphism in the type-A model -/

private def ringAutMulEquivAlgAut
    (F : Type*) [Field F] (p : Nat) [Fact p.Prime]
    [Algebra (ZMod p) F] :
    RingAut F ≃* (F ≃ₐ[ZMod p] F) where
  toFun f := AlgEquiv.ofRingEquiv (f := f) fun x => by
    obtain ⟨n, rfl⟩ := ZMod.intCast_surjective x
    simp
  invFun g := g.toRingEquiv
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- The ring Frobenius has the expected order over the prime field. -/
private theorem orderOf_frobeniusEquiv_eq_finrank
    {F : Type*} [Field F] [Finite F]
    (p : Nat) [Fact p.Prime] [CharP F p] [Algebra (ZMod p) F] :
    orderOf (frobeniusEquiv F p) = Module.finrank (ZMod p) F := by
  let toAlg := ringAutMulEquivAlgAut F p
  have hmap : toAlg (frobeniusEquiv F p) =
      FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) F := by
    ext x
    change x ^ p = x ^ Fintype.card (ZMod p)
    rw [ZMod.card]
  calc
    orderOf (frobeniusEquiv F p) =
        orderOf (toAlg (frobeniusEquiv F p)) :=
      (orderOf_injective toAlg.toMonoidHom toAlg.injective _).symm
    _ = orderOf
        (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) F) := by
      rw [hmap]
    _ = Module.finrank (ZMod p) F :=
      FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic (ZMod p) F

/-- Cardinal coordinates identify the order of Frobenius with the displayed
finite-field degree. -/
theorem orderOf_frobeniusEquiv_eq_of_card_eq_two_pow
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (n : Nat) (hcard : Nat.card F = 2 ^ n) :
    orderOf (frobeniusEquiv F 2) = n := by
  letI : Algebra (ZMod 2) F := ZMod.algebra F 2
  rw [orderOf_frobeniusEquiv_eq_finrank 2]
  apply Nat.pow_right_injective (by omega : 2 ≤ 2)
  calc
    2 ^ Module.finrank (ZMod 2) F = Nat.card F := by
      simpa only [Nat.card_zmod] using
        (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := F)).symm
    _ = 2 ^ n := hcard

/-- Every Frobenius power has odd order when the field degree is odd. -/
theorem frobeniusPower_orderOf_odd_of_card_eq_two_pow
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (n r : Nat) (hcard : Nat.card F = 2 ^ n) (hnodd : Odd n) :
    Odd (orderOf ((frobeniusEquiv F 2) ^ r)) := by
  have hdvd := orderOf_pow_dvd (x := frobeniusEquiv F 2) r
  rw [orderOf_frobeniusEquiv_eq_of_card_eq_two_pow n hcard] at hdvd
  exact hnodd.of_dvd_nat hdvd

/-- A nonzero exponent strictly below the field degree gives a nontrivial
Frobenius power. -/
theorem frobeniusPower_ne_one_of_fin
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    {n : Nat} [NeZero n]
    (hcard : Nat.card F = 2 ^ n) (r : Fin n) (hr : r ≠ 0) :
    (frobeniusEquiv F 2) ^ r.val ≠ 1 := by
  intro hphi
  have hdvdOrder : orderOf (frobeniusEquiv F 2) ∣ r.val :=
    orderOf_dvd_iff_pow_eq_one.mpr hphi
  have hdvd : n ∣ r.val := by
    simpa only [orderOf_frobeniusEquiv_eq_of_card_eq_two_pow n hcard]
      using hdvdOrder
  have hrzero : r.val = 0 := Nat.eq_zero_of_dvd_of_lt hdvd r.isLt
  apply hr
  apply Fin.ext
  simpa using hrzero

/-- For odd modulus, `r + r ≠ 0` follows from `r ≠ 0`. -/
theorem fin_add_self_ne_zero_of_odd
    {n : Nat} [NeZero n] (hnodd : Odd n)
    (r : Fin n) (hr : r ≠ 0) :
    r + r ≠ 0 := by
  intro hrr
  have hmod : n ∣ 2 * r.val := by
    apply Nat.dvd_iff_mod_eq_zero.mpr
    have hval := congrArg Fin.val hrr
    simpa [Fin.val_add, two_mul] using hval
  have hnCoprime : n.Coprime 2 :=
    Nat.coprime_two_right.mpr hnodd
  have hdvd : n ∣ r.val := hnCoprime.dvd_of_dvd_mul_left hmod
  have hrzero : r.val = 0 := Nat.eq_zero_of_dvd_of_lt hdvd r.isLt
  apply hr
  apply Fin.ext
  simpa using hrzero

/-! ## Actual lower-central extension coordinates -/

/-- The zeroth lower-central term is the ambient group. -/
private noncomputable def lowerCentralTermZeroEquivAmbient
    (P : Type uP) [Group P] :
    lowerCentralTerm P 0 ≃* P :=
  (MulEquiv.subgroupCongr (by simp [lowerCentralTerm])).trans
    Subgroup.topEquiv

/-- Under the square-layer identity, the ambient first lower-central term
maps to the kernel defining the zeroth lower-central layer. -/
private theorem lowerCentralTerm_one_map_zeroEquiv_symm
    (P : Type uP) [Group P]
    (hK0 : lowerCentralLayerKernel P 0 =
      (lowerCentralTerm P 1).subgroupOf (lowerCentralTerm P 0)) :
    (lowerCentralTerm P 1).map
        (lowerCentralTermZeroEquivAmbient P).symm =
      lowerCentralLayerKernel P 0 := by
  rw [hK0]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [lowerCentralTermZeroEquivAmbient, Subgroup.mem_subgroupOf] using hy
  · intro hx
    rw [Subgroup.mem_subgroupOf] at hx
    refine ⟨(x : P), hx, ?_⟩
    apply Subtype.ext
    rfl

/-- Identify the ambient quotient by the first lower-central term with the
actual zeroth lower-central layer. -/
private noncomputable def ambientQuotientEquivLowerCentralLayerZero
    (P : Type uP) [Group P]
    (hK0 : lowerCentralLayerKernel P 0 =
      (lowerCentralTerm P 1).subgroupOf (lowerCentralTerm P 0)) :
    P ⧸ lowerCentralTerm P 1 ≃* lowerCentralLayer P 0 :=
  QuotientGroup.congr _ _
    (lowerCentralTermZeroEquivAmbient P).symm
    (lowerCentralTerm_one_map_zeroEquiv_symm P hK0)

/-- When the second-layer denominator is trivial, the second layer is the
actual first lower-central term. -/
private noncomputable def lowerCentralLayerOneEquivTerm
    {P : Type uP} [Group P]
    (hK1 : lowerCentralLayerKernel P 1 = ⊥) :
    lowerCentralLayer P 1 ≃* lowerCentralTerm P 1 :=
  (QuotientGroup.quotientMulEquivOfEq hK1).trans
    QuotientGroup.quotientBot

/-- Kernel coordinates induced by an additive second-layer coordinate. -/
private noncomputable def lowerCentralExtensionLeft
    {P : Type uP} [Group P]
    {F : Type uF} [AddGroup F]
    (hK1 : lowerCentralLayerKernel P 1 = ⊥)
    (eOne : Additive (lowerCentralLayer P 1) ≃+ F) :
    Multiplicative F ≃* lowerCentralTerm P 1 :=
  (AddEquiv.toMultiplicativeLeft eOne.symm).trans
    (lowerCentralLayerOneEquivTerm hK1)

/-- Quotient coordinates induced by an additive zeroth-layer coordinate. -/
private noncomputable def lowerCentralExtensionRight
    {P : Type uP} [Group P]
    {F : Type uF} [AddGroup F]
    (hK0 : lowerCentralLayerKernel P 0 =
      (lowerCentralTerm P 1).subgroupOf (lowerCentralTerm P 0))
    (eZero : Additive (lowerCentralLayer P 0) ≃+ F) :
    P ⧸ lowerCentralTerm P 1 ≃* Multiplicative F :=
  (ambientQuotientEquivLowerCentralLayerZero P hK0).trans
    (AddEquiv.toMultiplicativeRight eZero)

/-- The kernel coordinate sends an actual second-layer square class back to
the ambient square. -/
private theorem lowerCentralExtensionLeft_square
    {P : Type uP} [Group P]
    {F : Type uF} [AddGroup F]
    (hSq : LowerCentralSquaresLieInSecond P)
    (hK1 : lowerCentralLayerKernel P 1 = ⊥)
    (eOne : Additive (lowerCentralLayer P 1) ≃+ F)
    (x : lowerCentralTerm P 0) :
    (x : P) ^ 2 = lowerCentralExtensionLeft hK1 eOne
      (Multiplicative.ofAdd
        (eOne (lowerCentralSquareMapAdditive P hSq
          (Additive.ofMul
            (QuotientGroup.mk' (lowerCentralLayerKernel P 0) x))))) := by
  change (x : P) ^ 2 =
    (((QuotientGroup.quotientMulEquivOfEq hK1).trans
      QuotientGroup.quotientBot)
      (Additive.toMul
        (eOne.symm
          (eOne (lowerCentralSquareMapAdditive P hSq
            (Additive.ofMul
              (QuotientGroup.mk' (lowerCentralLayerKernel P 0) x)))))) :
        lowerCentralTerm P 1)
  rw [eOne.symm_apply_apply, lowerCentralSquareMapAdditive_mk]
  rfl

/-- Xi-length two and additive coordinates on the two actual lower-central
layers produce the multiplicative kernel and quotient coordinates required by
`GroupExtension.ofNormalSubgroupCoordinates`. -/
theorem exists_lowerCentralExtensionCoordinates_of_xiLengthTwo
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    {F : Type uF} [AddGroup F]
    (hP : IsPGroup 2 P)
    (hncomm : ¬ IsMulCommutative P)
    (hxi : IsXiActor Y)
    (hlen : HasXiLengthTwo Y.subtype)
    (eZero : Additive (lowerCentralLayer P 0) ≃+ F)
    (eOne : Additive (lowerCentralLayer P 1) ≃+ F) :
    ∃ (left : Multiplicative F ≃* lowerCentralTerm P 1)
      (right : P ⧸ lowerCentralTerm P 1 ≃* Multiplicative F),
      (GroupExtension.ofNormalSubgroupCoordinates
        (lowerCentralTerm P 1) left right).inl.range =
          lowerCentralTerm P 1 := by
  have hSq : LowerCentralSquaresLieInSecond P :=
    lowerCentralSquaresLieInSecond_of_agemo_eq P
      (agemo_one_eq_lowerCentralTerm_one hP hncomm hxi hlen)
  have hK0 : lowerCentralLayerKernel P 0 =
      (lowerCentralTerm P 1).subgroupOf (lowerCentralTerm P 0) :=
    lowerCentralLayerKernel_zero_eq_of_squares_le P hSq
  have hAmbientK1 : lowerCentralLayerKernelInAmbient P 1 = ⊥ := by
    rw [lowerCentralLayerKernelInAmbient_eq,
      show 1 + 1 = 2 by omega,
      lowerCentralTerm_two_eq_bot hP hncomm hxi hlen, sup_bot_eq,
      lowerCentralTerm_one_eq_frattini hP hncomm hxi hlen,
      frattini_agemo_one_map_eq_bot hP hncomm hxi hlen]
  have hK1 : lowerCentralLayerKernel P 1 = ⊥ := by
    rw [← lowerCentralLayerKernelInAmbient_subgroupOf P 1, hAmbientK1]
    simp
  let left : Multiplicative F ≃* lowerCentralTerm P 1 :=
    lowerCentralExtensionLeft hK1 eOne
  let right : P ⧸ lowerCentralTerm P 1 ≃* Multiplicative F :=
    lowerCentralExtensionRight hK0 eZero
  exact ⟨left, right,
    GroupExtension.ofNormalSubgroupCoordinates_range_inl
      (lowerCentralTerm P 1) left right⟩

/-! ## Absorbing the nonzero square coefficient -/

/-- Absorb the nonzero scalar in a type-A square formula into the kernel
coordinate of the central extension. -/
noncomputable def typeADataOfScaledSquareCoordinates
    {P : Type uP} [Group P]
    {F : Type uF} [Field F] [Finite F] [CharP F 2]
    (parameter : Nat) (parameter_pos : 0 < parameter)
    (card_field : Nat.card F = 2 ^ parameter)
    (phi : RingAut F) (phi_ne_one : phi ≠ 1)
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
    TypeAData P := by
  let epsilonUnit : Fˣ := Units.mk0 epsilon hepsilon
  let scaleAdd : F ≃+ F :=
    (epsilonUnit.mulLeftLinearEquiv F F).toAddEquiv
  let scale : Multiplicative F ≃* Multiplicative F :=
    AddEquiv.toMultiplicative scaleAdd
  let left' : Multiplicative F ≃* N := scale.trans left
  let S : GroupExtension (Multiplicative F) P (Multiplicative F) :=
    GroupExtension.ofNormalSubgroupCoordinates N left' right
  apply TypeAData.ofExtension parameter parameter_pos card_field
    phi phi_ne_one phi_orderOf_odd S
  · simpa only [S, GroupExtension.ofNormalSubgroupCoordinates_range_inl]
      using hcentral
  · intro x
    rw [hsq x]
    rfl

/-! ## From the anchored trace formula to the square normal form -/

/-- A degree-one anchored trace formula for the actual lower-central square
map becomes the type-A square normal form after changing the first-layer
coordinate by the anchor Frobenius. -/
theorem exists_lowerCentralCoordinates_typeANormalForm_of_anchoredTrace_finrankOne
    {P : Type uP} [Group P]
    {K : Type uK} {L : Type uL}
    [Field K] [Field L] [Finite K] [Finite L]
    [CharP K 2] [CharP L 2] [Algebra K L]
    (hfin : Module.finrank K L = 1)
    (hSq : LowerCentralSquaresLieInSecond P)
    (eZero : Additive (lowerCentralLayer P 0) ≃+ L)
    (eOneK : Additive (lowerCentralLayer P 1) ≃+ K)
    (a r : Nat) (epsilon : L)
    (hformula : ∀ alpha : L,
      lowerCentralSquareMapAdditive P hSq (eZero.symm alpha) =
        eOneK.symm
          (Algebra.trace K L
            (alpha ^ (2 ^ a) *
              (alpha ^ (2 ^ a)) ^ (2 ^ r) * epsilon))) :
    ∃ eZero' : Additive (lowerCentralLayer P 0) ≃+ L,
      ∃ eOneL : Additive (lowerCentralLayer P 1) ≃+ L,
        ∀ beta : L,
          eOneL
              (lowerCentralSquareMapAdditive P hSq
                (eZero'.symm beta)) =
            epsilon *
              (beta * ((frobeniusEquiv L 2) ^ r) beta) := by
  let anchor : RingAut L := (frobeniusEquiv L 2) ^ a
  let eZero' : Additive (lowerCentralLayer P 0) ≃+ L :=
    eZero.trans anchor.toAddEquiv
  let eOneL : Additive (lowerCentralLayer P 1) ≃+ L :=
    eOneK.trans (finrankOneRingEquiv K L hfin).toAddEquiv
  refine ⟨eZero', eOneL, ?_⟩
  intro beta
  let alpha : L := anchor.symm beta
  have hfrobenius (x : L) (t : Nat) :
      x ^ (2 ^ t) = ((frobeniusEquiv L 2) ^ t) x := by
    rw [← iterateFrobeniusEquiv_eq_pow]
    exact (iterateFrobeniusEquiv_def L 2 t x).symm
  have hanchor : alpha ^ (2 ^ a) = beta := by
    rw [hfrobenius]
    exact anchor.apply_symm_apply beta
  calc
    eOneL
          (lowerCentralSquareMapAdditive P hSq
            (eZero'.symm beta)) =
        algebraMap K L
          (Algebra.trace K L
            (alpha ^ (2 ^ a) *
              (alpha ^ (2 ^ a)) ^ (2 ^ r) * epsilon)) := by
      change algebraMap K L
          (eOneK
            (lowerCentralSquareMapAdditive P hSq
              (eZero.symm (anchor.symm beta)))) = _
      rw [hformula alpha]
      simp only [AddEquiv.apply_symm_apply]
    _ = alpha ^ (2 ^ a) *
          (alpha ^ (2 ^ a)) ^ (2 ^ r) * epsilon :=
      algebraMap_trace_eq_self_of_finrank_eq_one K L hfin _
    _ = epsilon *
          (beta * ((frobeniusEquiv L 2) ^ r) beta) := by
      rw [hanchor, hfrobenius]
      ac_rfl

/-! ## The actual square normal form gives type A -/

/-- **Higman Lemma 11 (p. 89), lower-central extension endgame.**

An actual xi-length-two lower-central square normal form supplies all data of
a Peterfalvi type-A Suzuki `2`-group.  The theorem constructs both short
exact-sequence coordinates from the lower-central quotients; it does not posit
an abstract extension or a multiplication law. -/
noncomputable def typeADataOfLowerCentralSquareNormalForm
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    {F : Type uF} [Field F] [Finite F] [CharP F 2]
    (hP : IsPGroup 2 P)
    (hncomm : ¬ IsMulCommutative P)
    (hxi : IsXiActor Y)
    (hlen : HasXiLengthTwo Y.subtype)
    (parameter : ℕ)
    (parameter_pos : 0 < parameter)
    (card_field : Nat.card F = 2 ^ parameter)
    (phi : RingAut F)
    (phi_ne_one : phi ≠ 1)
    (phi_orderOf_odd : Odd (orderOf phi))
    (epsilon : F)
    (hepsilon : epsilon ≠ 0)
    (eZero : Additive (lowerCentralLayer P 0) ≃+ F)
    (eOne : Additive (lowerCentralLayer P 1) ≃+ F)
    (hnormal : ∀ alpha : F,
      eOne (lowerCentralSquareMapAdditive P
        (lowerCentralSquaresLieInSecond_of_agemo_eq P
          (agemo_one_eq_lowerCentralTerm_one hP hncomm hxi hlen))
        (eZero.symm alpha)) =
          epsilon * (alpha * phi alpha)) :
    TypeAData P := by
  let hSq : LowerCentralSquaresLieInSecond P :=
    lowerCentralSquaresLieInSecond_of_agemo_eq P
      (agemo_one_eq_lowerCentralTerm_one hP hncomm hxi hlen)
  have hK0 : lowerCentralLayerKernel P 0 =
      (lowerCentralTerm P 1).subgroupOf (lowerCentralTerm P 0) :=
    lowerCentralLayerKernel_zero_eq_of_squares_le P hSq
  have hAmbientK1 : lowerCentralLayerKernelInAmbient P 1 = ⊥ := by
    rw [lowerCentralLayerKernelInAmbient_eq,
      show 1 + 1 = 2 by omega,
      lowerCentralTerm_two_eq_bot hP hncomm hxi hlen, sup_bot_eq,
      lowerCentralTerm_one_eq_frattini hP hncomm hxi hlen,
      frattini_agemo_one_map_eq_bot hP hncomm hxi hlen]
  have hK1 : lowerCentralLayerKernel P 1 = ⊥ := by
    rw [← lowerCentralLayerKernelInAmbient_subgroupOf P 1, hAmbientK1]
    simp
  let left : Multiplicative F ≃* lowerCentralTerm P 1 :=
    lowerCentralExtensionLeft hK1 eOne
  let right : P ⧸ lowerCentralTerm P 1 ≃* Multiplicative F :=
    lowerCentralExtensionRight hK0 eZero
  have hcentral : lowerCentralTerm P 1 ≤ Subgroup.center P := by
    rw [lowerCentralTerm_one_eq_frattini hP hncomm hxi hlen,
      (commutator_eq_frattini_and_frattini_eq_center
        hP hncomm hxi hlen).2]
  have hsquareCoordinates : ∀ x : P, x ^ 2 =
      left (Multiplicative.ofAdd
        (epsilon *
          ((right (QuotientGroup.mk' (lowerCentralTerm P 1) x)).toAdd *
            phi (right
              (QuotientGroup.mk' (lowerCentralTerm P 1) x)).toAdd))) := by
    intro x
    let xZero : lowerCentralTerm P 0 :=
      ⟨x, by simp [lowerCentralTerm]⟩
    let alpha : F := eZero (Additive.ofMul
      (QuotientGroup.mk' (lowerCentralLayerKernel P 0) xZero))
    have hright :
        (right (QuotientGroup.mk' (lowerCentralTerm P 1) x)).toAdd =
          alpha := by
      rfl
    have hnormal' :
        eOne (lowerCentralSquareMapAdditive P hSq
          (Additive.ofMul
            (QuotientGroup.mk' (lowerCentralLayerKernel P 0) xZero))) =
          epsilon * (alpha * phi alpha) := by
      simpa only [hSq, alpha, eZero.symm_apply_apply] using hnormal alpha
    calc
      x ^ 2 = left (Multiplicative.ofAdd
          (eOne (lowerCentralSquareMapAdditive P hSq
            (Additive.ofMul
              (QuotientGroup.mk' (lowerCentralLayerKernel P 0)
                xZero))))) :=
        lowerCentralExtensionLeft_square hSq hK1 eOne xZero
      _ = left (Multiplicative.ofAdd
          (epsilon * (alpha * phi alpha))) := by rw [hnormal']
      _ = left (Multiplicative.ofAdd
          (epsilon *
            ((right
              (QuotientGroup.mk' (lowerCentralTerm P 1) x)).toAdd *
              phi (right
                (QuotientGroup.mk' (lowerCentralTerm P 1) x)).toAdd))) := by
        rw [hright]
  exact typeADataOfScaledSquareCoordinates (P := P) (F := F)
    parameter parameter_pos card_field phi phi_ne_one phi_orderOf_odd
    (lowerCentralTerm P 1) left right hcentral epsilon hepsilon
    hsquareCoordinates

end

end OddOrder.Higman.Suzuki2Groups
