/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.ExponentTwoAmbientBracketFaithfulness
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaTwelve.MixedEigenweights

/-!
# Higman's Lemma 13: ambient bracket zero implies commutativity

G. Higman, “Suzuki 2-groups,” *Illinois Journal of Mathematics* 7 (1963),
Lemma 13, p. 93.

When the denominator of the degree-one lower-central layer is trivial, the
lower-central bracket is faithful on actual commutators.  Thus vanishing of
the bracket of two actual zeroth-layer classes says that their representatives
commute in the ambient group.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

noncomputable section

open scoped commutatorElement IsMulCommutative

universe uP uM uN

local instance ambientBracketCommutativityLayerIsMulCommutative
    (P : Type uP) [Group P] (i : Nat) :
    IsMulCommutative (lowerCentralLayer P i) :=
  lowerCentralLayerIsMulCommutative P i

local instance ambientBracketCommutativityLayerCommGroup
    (P : Type uP) [Group P] (i : Nat) :
    CommGroup (lowerCentralLayer P i) :=
  { (inferInstance : Group (lowerCentralLayer P i)) with
    mul_comm := (lowerCentralLayer_isElementaryAbelian P i).comm }

noncomputable local instance ambientBracketCommutativityLayerZModTwoModule
    (P : Type uP) [Group P] (i : Nat) :
    Module (ZMod 2) (Additive (lowerCentralLayer P i)) :=
  lowerCentralLayerZmodModule P i

/-- The zeroth lower-central class of an actual ambient group element. -/
def ambientLayerZeroClass
    (P : Type uP) [Group P] (x : P) :
    Additive (lowerCentralLayer P 0) :=
  layerZeroClass ((lowerCentralTermZeroEquivAmbient P).symm x)

/-- If the degree-one lower-central denominator is trivial, vanishing of
the bracket of two actual zeroth-layer classes implies that the ambient
representatives commute. -/
theorem commute_of_lowerCentralCommutatorBilinear_eq_zero
    {P : Type uP} [Group P]
    (hK1 : lowerCentralLayerKernel P 1 = ⊥)
    (x y : P)
    (hzero :
      lowerCentralCommutatorBilinear P
          (ambientLayerZeroClass P x)
          (ambientLayerZeroClass P y) = 0) :
    Commute x y := by
  let x0 : lowerCentralTerm P 0 :=
    (lowerCentralTermZeroEquivAmbient P).symm x
  let y0 : lowerCentralTerm P 0 :=
    (lowerCentralTermZeroEquivAmbient P).symm y
  have hzero' :
      lowerCentralCommutatorBilinear P
          (layerZeroClass x0) (layerZeroClass y0) = 0 := by
    simpa [ambientLayerZeroClass, x0, y0] using hzero
  unfold layerZeroClass at hzero'
  rw [lowerCentralCommutatorBilinear_mk] at hzero'
  have hvalueOne : lowerCentralCommutatorValue P x0 y0 = 1 := by
    simpa using congrArg Additive.toMul hzero'
  have hmem : lowerCentralCommutator P x0 y0 ∈
      lowerCentralLayerKernel P 1 :=
    (QuotientGroup.eq_one_iff _).mp hvalueOne
  rw [hK1] at hmem
  have hsub : lowerCentralCommutator P x0 y0 = 1 :=
    Subgroup.mem_bot.mp hmem
  have hcommOne : ⁅(x0 : P), (y0 : P)⁆ = 1 := by
    simpa [lowerCentralCommutator] using congrArg Subtype.val hsub
  have hx0 : (x0 : P) = x := by
    change lowerCentralTermZeroEquivAmbient P x0 = x
    exact (lowerCentralTermZeroEquivAmbient P).apply_symm_apply x
  have hy0 : (y0 : P) = y := by
    change lowerCentralTermZeroEquivAmbient P y0 = y
    exact (lowerCentralTermZeroEquivAmbient P).apply_symm_apply y
  apply commutatorElement_eq_one_iff_commute.mp
  simpa only [hx0, hy0] using hcommOne

/-- Exponent two of the ambient Frattini subgroup supplies the trivial
degree-one denominator needed by bracket faithfulness. -/
theorem commute_of_lowerCentralCommutatorBilinear_eq_zero_of_exponent_two
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hncomm : ¬ IsMulCommutative P)
    (hxi : IsXiActor Y)
    (htwo : ∀ z : frattini P, z ^ 2 = 1)
    (x y : P)
    (hzero :
      lowerCentralCommutatorBilinear P
          (ambientLayerZeroClass P x)
          (ambientLayerZeroClass P y) = 0) :
    Commute x y :=
  commute_of_lowerCentralCommutatorBilinear_eq_zero
    (lowerCentralLayerKernel_one_eq_bot_of_exponent_two
      hP hncomm hxi htwo)
    x y hzero

/-- Pointwise representative form for linear families in the ambient
zeroth layer.  Equalities identifying two family values with actual quotient
classes transport bracket vanishing to commutativity of their representatives. -/
theorem commute_of_represented_lowerCentralCommutatorBilinear_eq_zero
    {P : Type uP} [Group P]
    {M : Type uM} {N : Type uN}
    [AddCommMonoid M] [Module (ZMod 2) M]
    [AddCommMonoid N] [Module (ZMod 2) N]
    (hK1 : lowerCentralLayerKernel P 1 = ⊥)
    (iU : M →ₗ[ZMod 2] Additive (lowerCentralLayer P 0))
    (iW : N →ₗ[ZMod 2] Additive (lowerCentralLayer P 0))
    (alpha : M) (beta : N) (x y : P)
    (hx : iU alpha = ambientLayerZeroClass P x)
    (hy : iW beta = ambientLayerZeroClass P y)
    (hzero : lowerCentralCommutatorBilinear P
      (iU alpha) (iW beta) = 0) :
    Commute x y := by
  apply commute_of_lowerCentralCommutatorBilinear_eq_zero hK1 x y
  rw [← hx, ← hy]
  exact hzero

/-- Family form of bracket faithfulness for chosen actual representatives
of two linear-map families. -/
theorem pairwise_commute_of_represented_lowerCentralCommutatorBilinear_eq_zero
    {P : Type uP} [Group P]
    {M : Type uM} {N : Type uN}
    [AddCommMonoid M] [Module (ZMod 2) M]
    [AddCommMonoid N] [Module (ZMod 2) N]
    (hK1 : lowerCentralLayerKernel P 1 = ⊥)
    (iU : M →ₗ[ZMod 2] Additive (lowerCentralLayer P 0))
    (iW : N →ₗ[ZMod 2] Additive (lowerCentralLayer P 0))
    (x : M → P) (y : N → P)
    (hx : ∀ alpha, iU alpha = ambientLayerZeroClass P (x alpha))
    (hy : ∀ beta, iW beta = ambientLayerZeroClass P (y beta))
    (hzero : ∀ alpha beta,
      lowerCentralCommutatorBilinear P
        (iU alpha) (iW beta) = 0) :
    ∀ alpha beta, Commute (x alpha) (y beta) := by
  intro alpha beta
  exact commute_of_represented_lowerCentralCommutatorBilinear_eq_zero
    hK1 iU iW alpha beta (x alpha) (y beta)
      (hx alpha) (hy beta) (hzero alpha beta)

end

end OddOrder.Higman.Suzuki2Groups
