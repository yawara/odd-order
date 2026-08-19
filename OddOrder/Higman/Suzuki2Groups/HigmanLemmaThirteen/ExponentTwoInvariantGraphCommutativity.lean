/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.ExponentTwoAmbientBracketCommutativity
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.ExponentTwoInvariantGraphPreimage

/-!
# Higman's Lemma 13: invariant graph factors commute with the common factor

G. Higman, “Suzuki 2-groups,” *Illinois Journal of Mathematics* 7 (1963),
Lemma 13, p. 93.

A primitive left eigenvalue propagates one seed bracket cancellation across
the whole left coordinate field.  A nonzero right eigenvalue lets the right
coordinate be reparameterized while applying the same actor power.  Quotient
range descriptions then lift this family cancellation to elementwise
commutativity of the actual canonical graph preimage and common factor.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

open OddOrder.GroupTheory
open OddOrder.Isaacs.Ch03
open scoped IsMulCommutative

noncomputable section

universe uP

local instance invariantGraphCommutativityLayerIsMulCommutative
    (P : Type uP) [Group P] (i : Nat) :
    IsMulCommutative (lowerCentralLayer P i) :=
  lowerCentralLayerIsMulCommutative P i

local instance invariantGraphCommutativityLayerCommGroup
    (P : Type uP) [Group P] (i : Nat) :
    CommGroup (lowerCentralLayer P i) :=
  { (inferInstance : Group (lowerCentralLayer P i)) with
    mul_comm := (lowerCentralLayer_isElementaryAbelian P i).comm }

noncomputable local instance invariantGraphCommutativityLayerZModTwoModule
    (P : Type uP) [Group P] (i : Nat) :
    Module (ZMod 2) (Additive (lowerCentralLayer P i)) :=
  lowerCentralLayerZmodModule P i

/-- A generator eigen-equation propagates to every nonnegative power of
the generator. -/
theorem lowerCentralLayerRepresentation_eigen_pow
    {P : Type uP} [Group P]
    {Y : Subgroup (MulAut P)}
    {n : Nat}
    (c : Y)
    (i : GaloisField 2 n →ₗ[ZMod 2]
      Additive (lowerCentralLayer P 0))
    (lambda : GaloisField 2 n)
    (heigen : ∀ alpha,
      lowerCentralLayerRepresentation Y.subtype 0 c (i alpha) =
        i (lambda * alpha))
    (k : Nat) (alpha : GaloisField 2 n) :
    lowerCentralLayerRepresentation Y.subtype 0 (c ^ k) (i alpha) =
      i (lambda ^ k * alpha) := by
  induction k with
  | zero => simp
  | succ k ih =>
      simp only [pow_succ', map_mul, Module.End.mul_apply]
      rw [ih, heigen, mul_assoc]

/-- A seed cancellation on `iU 1` propagates across two eigenfamilies when
the left eigenvalue is primitive and the right eigenvalue is nonzero. -/
theorem lowerCentralCommutatorBilinear_eq_zero_of_primitive_left_eigen_seed
    {P : Type uP} [Group P]
    {Y : Subgroup (MulAut P)}
    {n : Nat}
    (hn : n ≠ 0)
    (c : Y)
    (iU iW : GaloisField 2 n →ₗ[ZMod 2]
      Additive (lowerCentralLayer P 0))
    (lambda mu : GaloisField 2 n)
    (hlambda : IsPrimitiveRoot lambda (2 ^ n - 1))
    (hmu : mu ≠ 0)
    (hUeigen : ∀ alpha,
      lowerCentralLayerRepresentation Y.subtype 0 c (iU alpha) =
        iU (lambda * alpha))
    (hWeigen : ∀ beta,
      lowerCentralLayerRepresentation Y.subtype 0 c (iW beta) =
        iW (mu * beta))
    (hseed : ∀ beta,
      lowerCentralCommutatorBilinear P (iU 1) (iW beta) = 0) :
    ∀ alpha beta,
      lowerCentralCommutatorBilinear P (iU alpha) (iW beta) = 0 := by
  have hNpos : 0 < 2 ^ n - 1 := by
    have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    have hpowTwo : 2 ^ 1 ≤ 2 ^ n :=
      Nat.pow_le_pow_right (by norm_num) hnpos
    omega
  let : NeZero (2 ^ n - 1) := ⟨hNpos.ne'⟩
  have hcard : Nat.card (GaloisField 2 n) = 2 ^ n :=
    GaloisField.card 2 n hn
  let : Fintype (GaloisField 2 n) := Fintype.ofFinite _
  have hequivariant (g : Y)
      (u v : Additive (lowerCentralLayer P 0)) :
      lowerCentralLayerRepresentation Y.subtype 1 g
          (lowerCentralCommutatorBilinear P u v) =
        lowerCentralCommutatorBilinear P
          (lowerCentralLayerRepresentation Y.subtype 0 g u)
          (lowerCentralLayerRepresentation Y.subtype 0 g v) := by
    have hu :
        lowerCentralLayerRepresentation Y.subtype 0 g u =
          Additive.ofMul
            (lowerCentralLayerAction Y.subtype 0 g u.toMul) := by
      change lowerCentralLayerRepresentation Y.subtype 0 g
          (Additive.ofMul u.toMul) =
        Additive.ofMul
          (lowerCentralLayerAction Y.subtype 0 g u.toMul)
      exact lowerCentralLayerRepresentation_apply Y.subtype 0 g u.toMul
    have hv :
        lowerCentralLayerRepresentation Y.subtype 0 g v =
          Additive.ofMul
            (lowerCentralLayerAction Y.subtype 0 g v.toMul) := by
      change lowerCentralLayerRepresentation Y.subtype 0 g
          (Additive.ofMul v.toMul) =
        Additive.ofMul
          (lowerCentralLayerAction Y.subtype 0 g v.toMul)
      exact lowerCentralLayerRepresentation_apply Y.subtype 0 g v.toMul
    rw [hu, hv]
    exact lowerCentralCommutatorBilinear_equivariant Y.subtype g u v
  intro alpha beta
  by_cases halpha : alpha = 0
  · subst alpha
    simp
  · have halphaPow : alpha ^ (2 ^ n - 1) = 1 := by
      have h := FiniteField.pow_card_sub_one_eq_one alpha halpha
      rwa [← Nat.card_eq_fintype_card, hcard] at h
    obtain ⟨k, _hk, hk⟩ :=
      hlambda.eq_pow_of_pow_eq_one halphaPow
    rw [← hk]
    let gamma : GaloisField 2 n := mu⁻¹ ^ k * beta
    have hmuPow : mu ^ k * gamma = beta := by
      dsimp only [gamma]
      rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ hmu,
        one_pow, one_mul]
    calc
      lowerCentralCommutatorBilinear P
          (iU (lambda ^ k)) (iW beta) =
          lowerCentralCommutatorBilinear P
            (iU (lambda ^ k * 1)) (iW (mu ^ k * gamma)) := by
              rw [mul_one, hmuPow]
      _ = lowerCentralCommutatorBilinear P
            (lowerCentralLayerRepresentation Y.subtype 0 (c ^ k) (iU 1))
            (lowerCentralLayerRepresentation Y.subtype 0 (c ^ k)
              (iW gamma)) := by
              rw [lowerCentralLayerRepresentation_eigen_pow
                c iU lambda hUeigen k 1,
                lowerCentralLayerRepresentation_eigen_pow
                  c iW mu hWeigen k gamma]
      _ = lowerCentralLayerRepresentation Y.subtype 1 (c ^ k)
            (lowerCentralCommutatorBilinear P (iU 1) (iW gamma)) :=
          (hequivariant (c ^ k) (iU 1) (iW gamma)).symm
      _ = 0 := by rw [hseed, map_zero]

/-- The canonical map from the zeroth lower-central layer sends the class
of an actual ambient element to its ordinary Frattini quotient class. -/
@[simp]
theorem layerZeroToFrattiniQuotientLinear_ambientLayerZeroClass
    {P : Type uP} [Group P] [Finite P]
    (hP : IsPGroup 2 P) (x : P) :
    letI : CommGroup (P ⧸ frattini P) :=
      frattiniQuotientCommGroup P hP
    letI : Module (ZMod 2) (Additive (P ⧸ frattini P)) :=
      frattiniQuotientZModTwoModule P hP
    layerZeroToFrattiniQuotientLinear P hP
        (ambientLayerZeroClass P x) =
      Additive.ofMul (QuotientGroup.mk' (frattini P) x) := by
  let : CommGroup (P ⧸ frattini P) :=
    frattiniQuotientCommGroup P hP
  let : Module (ZMod 2) (Additive (P ⧸ frattini P)) :=
    frattiniQuotientZModTwoModule P hP
  rw [ambientLayerZeroClass, layerZeroClass,
    layerZeroToFrattiniQuotientLinear_apply,
    toMul_ofMul, layerZeroToQuotient_mk]
  apply congrArg Additive.ofMul
  apply congrArg (QuotientGroup.mk' (frattini P))
  change lowerCentralTermZeroEquivAmbient P
    ((lowerCentralTermZeroEquivAmbient P).symm x) = x
  exact (lowerCentralTermZeroEquivAmbient P).apply_symm_apply x

/-- **Higman Lemma 13 (p. 93), graph/common-factor commutativity.**

If the quotient image of `U` is the range of the left eigenfamily and the
quotient image of `W` is the range of the right eigenfamily, one seed bracket
cancellation propagates to every pair of coordinates and hence every actual
pair of elements of `U` and `W` commutes. -/
theorem invariantGraphPreimage_commutes_of_primitive_eigen_seed
    {P : Type uP} [Group P] [Finite P]
    {Y : Subgroup (MulAut P)}
    (hP : IsPGroup 2 P)
    (hncomm : ¬ IsMulCommutative P)
    (hxi : IsXiActor Y)
    (htwo : ∀ z : frattini P, z ^ 2 = 1)
    {n : Nat}
    (hn : n ≠ 0)
    (c : Y)
    (iU iW : GaloisField 2 n →ₗ[ZMod 2]
      Additive (lowerCentralLayer P 0))
    (lambda mu : GaloisField 2 n)
    (hlambda : IsPrimitiveRoot lambda (2 ^ n - 1))
    (hmu : mu ≠ 0)
    (hUeigen : ∀ alpha,
      lowerCentralLayerRepresentation Y.subtype 0 c (iU alpha) =
        iU (lambda * alpha))
    (hWeigen : ∀ beta,
      lowerCentralLayerRepresentation Y.subtype 0 c (iW beta) =
        iW (mu * beta))
    (hseed : ∀ beta,
      lowerCentralCommutatorBilinear P (iU 1) (iW beta) = 0) :
    letI : CommGroup (P ⧸ frattini P) :=
      frattiniQuotientCommGroup P hP
    letI : Module (ZMod 2) (Additive (P ⧸ frattini P)) :=
      frattiniQuotientZModTwoModule P hP
    ∀ (U W : Subgroup P),
      U.map (QuotientGroup.mk' (frattini P)) =
        elabSubmoduleSubgroupEquiv 2
          (LinearMap.range
            ((layerZeroToFrattiniQuotientLinear P hP).comp iU)) →
      LinearMap.range
          ((layerZeroToFrattiniQuotientLinear P hP).comp iW) =
        (elabSubmoduleSubgroupEquiv 2).symm
          (W.map (QuotientGroup.mk' (frattini P))) →
      ∀ u ∈ U, ∀ w ∈ W, Commute u w := by
  let : CommGroup (P ⧸ frattini P) :=
    frattiniQuotientCommGroup P hP
  let : Module (ZMod 2) (Additive (P ⧸ frattini P)) :=
    frattiniQuotientZModTwoModule P hP
  intro U W hUmap hWrange u hu w hw
  have hbracket :=
    lowerCentralCommutatorBilinear_eq_zero_of_primitive_left_eigen_seed
      hn c iU iW lambda mu hlambda hmu hUeigen hWeigen hseed
  have huMap :
      QuotientGroup.mk' (frattini P) u ∈
        U.map (QuotientGroup.mk' (frattini P)) :=
    Subgroup.mem_map_of_mem _ hu
  rw [hUmap] at huMap
  have huRange :
      Additive.ofMul (QuotientGroup.mk' (frattini P) u) ∈
        LinearMap.range
          ((layerZeroToFrattiniQuotientLinear P hP).comp iU) :=
    (mem_elabSubmoduleSubgroupEquiv _ _).1 huMap
  obtain ⟨alpha, halpha⟩ := huRange
  have hwMap :
      QuotientGroup.mk' (frattini P) w ∈
        W.map (QuotientGroup.mk' (frattini P)) :=
    Subgroup.mem_map_of_mem _ hw
  have hwRange :
      Additive.ofMul (QuotientGroup.mk' (frattini P) w) ∈
        LinearMap.range
          ((layerZeroToFrattiniQuotientLinear P hP).comp iW) := by
    rw [hWrange]
    apply (mem_symm_elabSubmoduleSubgroupEquiv
      (W.map (QuotientGroup.mk' (frattini P))) _).2
    simpa using hwMap
  obtain ⟨beta, hbeta⟩ := hwRange
  have hiU : iU alpha = ambientLayerZeroClass P u := by
    apply layerZeroToFrattiniQuotientLinear_injective P hP
    calc
      layerZeroToFrattiniQuotientLinear P hP (iU alpha) =
          ((layerZeroToFrattiniQuotientLinear P hP).comp iU) alpha := rfl
      _ = Additive.ofMul (QuotientGroup.mk' (frattini P) u) := halpha
      _ = layerZeroToFrattiniQuotientLinear P hP
          (ambientLayerZeroClass P u) :=
        (layerZeroToFrattiniQuotientLinear_ambientLayerZeroClass hP u).symm
  have hiW : iW beta = ambientLayerZeroClass P w := by
    apply layerZeroToFrattiniQuotientLinear_injective P hP
    calc
      layerZeroToFrattiniQuotientLinear P hP (iW beta) =
          ((layerZeroToFrattiniQuotientLinear P hP).comp iW) beta := rfl
      _ = Additive.ofMul (QuotientGroup.mk' (frattini P) w) := hbeta
      _ = layerZeroToFrattiniQuotientLinear P hP
          (ambientLayerZeroClass P w) :=
        (layerZeroToFrattiniQuotientLinear_ambientLayerZeroClass hP w).symm
  exact commute_of_represented_lowerCentralCommutatorBilinear_eq_zero
    (lowerCentralLayerKernel_one_eq_bot_of_exponent_two
      hP hncomm hxi htwo)
    iU iW alpha beta u w hiU hiW (hbracket alpha beta)

end

end OddOrder.Higman.Suzuki2Groups
