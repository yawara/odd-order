/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLowerCentralSpectrum
import Mathlib.LinearAlgebra.QuadraticForm.Basis
import Mathlib.Algebra.CharP.Two

/-!
# Higman's square map on the first lower-central layer

G. Higman, *Suzuki 2-groups*, Illinois J. Math. 7 (1963), Lemma 5,
pp. 84--85; used in Peterfalvi, Appendix III.

Under `H² = H₂`, squaring induces a quadratic map from Higman's first
lower-central layer `L₁` to `L₂`.  This file constructs that map, proves its
equivariance and polarization by the commutator pairing, and records Higman's
uniqueness argument after scalar extension.  A normalized
Frobenius-conjugate basis then identifies the actual square map with the
upper-triangular coordinate candidate and gives Higman's displayed polynomial.
-/

set_option autoImplicit false

open scoped TensorProduct commutatorElement IsMulCommutative BigOperators
open OddOrder.GroupTheory
open Module

namespace OddOrder.Higman.Suzuki2Groups

universe uH uK uMain

local instance instSquareMapLayerKernelInAmbientNormal
    (H : Type uH) [Group H] (i : ℕ) :
    (lowerCentralLayerKernelInAmbient H i).Normal :=
  lowerCentralLayerKernelInAmbient_normal H i

/-! ## The square map on lower-central layers -/

/-- The weakened hypothesis needed to descend squaring: the subgroup generated
by squares in `H₁` lies in `H₂`. Higman's source hypothesis `H² = H₂` implies
it via `lowerCentralSquaresLieInSecond_of_agemo_eq`. -/
def LowerCentralSquaresLieInSecond
    (H : Type uH) [Group H] : Prop :=
  (Agemo (↥(lowerCentralTerm H 0)) 2 1).map
      (lowerCentralTerm H 0).subtype ≤ lowerCentralTerm H 1

/-- Passing the square subgroup of the zeroth lower-central term back to the
ambient group recovers the ambient square subgroup. -/
theorem agemo_lowerCentralTerm_zero_map_eq
    (H : Type uH) [Group H] :
    (Agemo (↥(lowerCentralTerm H 0)) 2 1).map
        (lowerCentralTerm H 0).subtype = Agemo H 2 1 := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap, Agemo, Subgroup.closure_le]
    rintro x ⟨y, rfl⟩
    change (y : H) ^ (2 ^ 1) ∈ Agemo H 2 1
    exact Agemo.mem_of_eq_pow (y : H)
  · rw [Agemo, Subgroup.closure_le]
    rintro x ⟨y, rfl⟩
    apply Subgroup.mem_map.mpr
    let y₀ : ↥(lowerCentralTerm H 0) :=
      ⟨y, by simp [lowerCentralTerm]⟩
    refine ⟨y₀ ^ (2 ^ 1), Agemo.mem_of_eq_pow y₀, ?_⟩
    rfl

/-- Higman's source hypothesis `H² = H₂` implies the square-inclusion
hypothesis used by the construction below. -/
theorem lowerCentralSquaresLieInSecond_of_agemo_eq
    (H : Type uH) [Group H]
    (hAgemo : Agemo H 2 1 = lowerCentralTerm H 1) :
    LowerCentralSquaresLieInSecond H := by
  rw [LowerCentralSquaresLieInSecond,
    agemo_lowerCentralTerm_zero_map_eq, hAgemo]

/-- Under `H₁² ≤ H₂`, the first layer kernel is just `H₂`, viewed inside
`H₁`. -/
theorem lowerCentralLayerKernel_zero_eq_of_squares_le
    (H : Type uH) [Group H]
    (hSq : LowerCentralSquaresLieInSecond H) :
    lowerCentralLayerKernel H 0 =
      (lowerCentralTerm H 1).subgroupOf (lowerCentralTerm H 0) := by
  rw [← lowerCentralLayerKernelInAmbient_subgroupOf H 0,
    lowerCentralLayerKernelInAmbient_eq, sup_eq_right.mpr hSq]

/-- Ambient form of the preceding kernel identity. -/
theorem lowerCentralLayerKernelInAmbient_zero_eq_of_squares_le
    (H : Type uH) [Group H]
    (hSq : LowerCentralSquaresLieInSecond H) :
    lowerCentralLayerKernelInAmbient H 0 = lowerCentralTerm H 1 := by
  rw [lowerCentralLayerKernelInAmbient_eq, sup_eq_right.mpr hSq]

/-- The image of `H₂` in `H/(H₂²H₃)` is the commutator subgroup. -/
theorem lowerCentralTerm_one_map_layerKernelQuotient_eq_commutator
    (H : Type uH) [Group H] :
    (lowerCentralTerm H 1).map
        (QuotientGroup.mk' (lowerCentralLayerKernelInAmbient H 1)) =
      _root_.commutator
        (H ⧸ lowerCentralLayerKernelInAmbient H 1) := by
  rw [lowerCentralTerm, Subgroup.map_lowerCentralSeries,
    Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _),
    Subgroup.top_lowerCentralSeries_one]

/-- Squares of elements of `H₂` vanish modulo `H₂²H₃`. -/
theorem lowerCentralTerm_one_sq_mem_layerKernelInAmbient
    (H : Type uH) [Group H] (z : ↥(lowerCentralTerm H 1)) :
    (z : H) ^ 2 ∈ lowerCentralLayerKernelInAmbient H 1 := by
  rw [lowerCentralLayerKernelInAmbient_eq]
  apply (show (Agemo (↥(lowerCentralTerm H 1)) 2 1).map
      (lowerCentralTerm H 1).subtype ≤ _ from le_sup_left)
  refine ⟨z ^ 2, ?_, ?_⟩
  · simpa using
      (Agemo.mem_of_eq_pow (G := ↥(lowerCentralTerm H 1))
        (p := 2) (n := 1) z)
  · simp

/-- A representative square belongs to the second lower-central term. -/
def lowerCentralSquareRepresentative
    (H : Type uH) [Group H]
    (hSq : LowerCentralSquaresLieInSecond H)
    (x : ↥(lowerCentralTerm H 0)) : ↥(lowerCentralTerm H 1) :=
  ⟨(x : H) ^ 2, hSq <| by
    refine ⟨x ^ 2, ?_, ?_⟩
    · simpa using
        (Agemo.mem_of_eq_pow (G := ↥(lowerCentralTerm H 0))
          (p := 2) (n := 1) x)
    · simp⟩

/-- The square of a representative, reduced modulo `H₂² H₃`. -/
def lowerCentralSquareValue
    (H : Type uH) [Group H]
    (hSq : LowerCentralSquaresLieInSecond H)
    (x : ↥(lowerCentralTerm H 0)) : lowerCentralLayer H 1 :=
  QuotientGroup.mk' (lowerCentralLayerKernel H 1)
    (lowerCentralSquareRepresentative H hSq x)

/-- The square value is independent of the representative of the first
lower-central layer. -/
theorem lowerCentralSquareValue_eq_of_rel
    (H : Type uH) [Group H]
    (hSq : LowerCentralSquaresLieInSecond H)
    {x y : ↥(lowerCentralTerm H 0)}
    (hxy : QuotientGroup.leftRel (lowerCentralLayerKernel H 0) x y) :
    lowerCentralSquareValue H hSq x = lowerCentralSquareValue H hSq y := by
  have hxyK : x⁻¹ * y ∈ lowerCentralLayerKernel H 0 :=
    QuotientGroup.leftRel_apply.mp hxy
  have hkH₂ : (((x⁻¹ * y : ↥(lowerCentralTerm H 0)) : H)) ∈
      lowerCentralTerm H 1 := by
    rw [← lowerCentralLayerKernelInAmbient_zero_eq_of_squares_le H hSq]
    exact ⟨x⁻¹ * y, hxyK, rfl⟩
  let k : ↥(lowerCentralTerm H 1) :=
    ⟨(x : H)⁻¹ * (y : H), by simpa using hkH₂⟩
  let π : H →* H ⧸ lowerCentralLayerKernelInAmbient H 1 :=
    QuotientGroup.mk' (lowerCentralLayerKernelInAmbient H 1)
  have hk_commutator : π (k : H) ∈
      _root_.commutator (H ⧸ lowerCentralLayerKernelInAmbient H 1) := by
    rw [← lowerCentralTerm_one_map_layerKernelQuotient_eq_commutator H]
    exact ⟨k, k.2, rfl⟩
  have hk_center : π (k : H) ∈
      Subgroup.center (H ⧸ lowerCentralLayerKernelInAmbient H 1) :=
    quotient_layerKernel_one_commutator_le_center H hk_commutator
  have hcomm : Commute (π (x : H)) (π (k : H)) :=
    Subgroup.mem_center_iff.mp hk_center (π (x : H))
  have hk_sq : (π (k : H)) ^ 2 = 1 := by
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr
      (lowerCentralTerm_one_sq_mem_layerKernelInAmbient H k)
  have hy : π (y : H) = π (x : H) * π (k : H) := by
    simp [π, k, map_mul]
  have hsq : (π (x : H)) ^ 2 = (π (y : H)) ^ 2 := by
    rw [hy, hcomm.mul_pow, hk_sq, mul_one]
  apply lowerCentralLayerOneToAmbientQuotient_injective H
  change π ((x : H) ^ 2) = π ((y : H) ^ 2)
  simpa only [map_pow] using hsq

/-- **Higman Lemma 5** (construction, p. 85). Squaring descends from `H₁`
to a map `L₁ → L₂` whenever the square subgroup of `H₁` lies in `H₂`. -/
noncomputable def lowerCentralSquareMap
    (H : Type uH) [Group H]
    (hSq : LowerCentralSquaresLieInSecond H) :
    lowerCentralLayer H 0 → lowerCentralLayer H 1 :=
  Quotient.lift (lowerCentralSquareValue H hSq)
    (fun _ _ hxy ↦ lowerCentralSquareValue_eq_of_rel H hSq hxy)

/-- The descended square map evaluates to the square class on
representatives. -/
@[simp]
theorem lowerCentralSquareMap_mk
    (H : Type uH) [Group H]
    (hSq : LowerCentralSquaresLieInSecond H)
    (x : ↥(lowerCentralTerm H 0)) :
    lowerCentralSquareMap H hSq
        (QuotientGroup.mk' (lowerCentralLayerKernel H 0) x) =
      lowerCentralSquareValue H hSq x := rfl

/-- Mapping a representative square value into the ambient class-two quotient
gives the square of the ambient representative. -/
@[simp]
theorem lowerCentralLayerOneToAmbientQuotient_squareValue
    (H : Type uH) [Group H]
    (hSq : LowerCentralSquaresLieInSecond H)
    (x : ↥(lowerCentralTerm H 0)) :
    lowerCentralLayerOneToAmbientQuotient H
        (lowerCentralSquareValue H hSq x) =
      QuotientGroup.mk' (lowerCentralLayerKernelInAmbient H 1)
        ((x : H) ^ 2) := by
  rfl

/-- In the elementary-abelian second layer, reversing a commutator does not
change its value. -/
theorem lowerCentralCommutatorValue_comm
    (H : Type uH) [Group H]
    (x y : ↥(lowerCentralTerm H 0)) :
    lowerCentralCommutatorValue H x y =
      lowerCentralCommutatorValue H y x := by
  let z := lowerCentralCommutatorValue H x y
  have hzSq : z ^ 2 = 1 := (lowerCentralLayer_isElementaryAbelian H 1).2 z
  have hzInv : z⁻¹ = z := by
    calc
      z⁻¹ = z⁻¹ * 1 := (mul_one _).symm
      _ = z⁻¹ * (z * z) := by rw [← pow_two, hzSq]
      _ = z := by group
  have hswap : z⁻¹ = lowerCentralCommutatorValue H y x := by
    change (QuotientGroup.mk' (lowerCentralLayerKernel H 1)
        (lowerCentralCommutator H x y))⁻¹ = _
    rw [← map_inv]
    apply congrArg (QuotientGroup.mk' (lowerCentralLayerKernel H 1))
    apply Subtype.ext
    exact commutatorElement_inv (x : H) (y : H)
  exact hzInv.symm.trans hswap

/-- The representative square value has polarization equal to the actual
lower-central commutator. -/
theorem lowerCentralSquareValue_mul
    (H : Type uH) [Group H]
    (hSq : LowerCentralSquaresLieInSecond H)
    (x y : ↥(lowerCentralTerm H 0)) :
    lowerCentralSquareValue H hSq (x * y) =
      lowerCentralSquareValue H hSq x *
        lowerCentralSquareValue H hSq y *
          lowerCentralCommutatorValue H x y := by
  apply lowerCentralLayerOneToAmbientQuotient_injective H
  simp only [map_mul,
    lowerCentralLayerOneToAmbientQuotient_squareValue,
    lowerCentralLayerOneToAmbientQuotient_commutatorValue]
  let pi : H →* H ⧸ lowerCentralLayerKernelInAmbient H 1 :=
    QuotientGroup.mk' (lowerCentralLayerKernelInAmbient H 1)
  let qx := pi (x : H)
  let qy := pi (y : H)
  let z := ⁅qy, qx⁆
  have hzCenter : z ∈ Subgroup.center
      (H ⧸ lowerCentralLayerKernelInAmbient H 1) :=
    quotient_layerKernel_one_commutator_le_center H
      (Subgroup.commutator_mem_commutator (Subgroup.mem_top _)
        (Subgroup.mem_top _))
  have hzComm : ∀ g, z * g = g * z :=
    fun g ↦ (Subgroup.mem_center_iff.mp hzCenter g).symm
  have hbase : qy * qx = z * qx * qy := by
    dsimp [z]
    rw [commutatorElement_def]
    group
  have hcollect : (qx * qy) ^ 2 = z * qx ^ 2 * qy ^ 2 := by
    calc
      (qx * qy) ^ 2 = qx * (qy * qx) * qy := by rw [pow_two]; group
      _ = qx * (z * qx * qy) * qy := by rw [hbase]
      _ = (qx * z) * qx * qy * qy := by group
      _ = (z * qx) * qx * qy * qy := by rw [← hzComm qx]
      _ = z * qx ^ 2 * qy ^ 2 := by rw [pow_two qx, pow_two qy]; group
  have hmove : z * qx ^ 2 * qy ^ 2 = qx ^ 2 * qy ^ 2 * z := by
    rw [hzComm (qx ^ 2), mul_assoc, hzComm (qy ^ 2), ← mul_assoc]
  have hswap : z = ⁅qx, qy⁆ := by
    simpa only [z, qx, qy,
      lowerCentralLayerOneToAmbientQuotient_commutatorValue] using
      congrArg (lowerCentralLayerOneToAmbientQuotient H)
        (lowerCentralCommutatorValue_comm H y x)
  change pi (((x * y : ↥(lowerCentralTerm H 0)) : H) ^ 2) =
    pi ((x : H) ^ 2) * pi ((y : H) ^ 2) * ⁅pi (x : H), pi (y : H)⁆
  calc
    pi (((x * y : ↥(lowerCentralTerm H 0)) : H) ^ 2) =
        (pi ((x : H) * (y : H))) ^ 2 := by rw [map_pow]; rfl
    _ = (qx * qy) ^ 2 := by rw [map_mul]
    _ = z * qx ^ 2 * qy ^ 2 := hcollect
    _ = qx ^ 2 * qy ^ 2 * z := hmove
    _ = qx ^ 2 * qy ^ 2 * ⁅qx, qy⁆ := by rw [hswap]
    _ = pi ((x : H) ^ 2) * pi ((y : H) ^ 2) *
        ⁅pi (x : H), pi (y : H)⁆ := by rw [map_pow, map_pow]

/-- Multiplicative form of the descended polarization law. -/
theorem lowerCentralSquareMap_mul
    (H : Type uH) [Group H]
    (hSq : LowerCentralSquaresLieInSecond H)
    (u v : lowerCentralLayer H 0) :
    lowerCentralSquareMap H hSq (u * v) =
      lowerCentralSquareMap H hSq u *
        lowerCentralSquareMap H hSq v *
          lowerCentralCommutatorBihom H u v := by
  obtain ⟨x, rfl⟩ :=
    QuotientGroup.mk'_surjective (lowerCentralLayerKernel H 0) u
  obtain ⟨y, rfl⟩ :=
    QuotientGroup.mk'_surjective (lowerCentralLayerKernel H 0) v
  rw [← (QuotientGroup.mk' (lowerCentralLayerKernel H 0)).map_mul x y]
  simpa only [lowerCentralSquareMap_mk, lowerCentralCommutatorBihom_mk] using
    lowerCentralSquareValue_mul H hSq x y

/-- The square map in the canonical additive notation. -/
noncomputable def lowerCentralSquareMapAdditive
    (H : Type uH) [Group H]
    (hSq : LowerCentralSquaresLieInSecond H) :
    Additive (lowerCentralLayer H 0) → Additive (lowerCentralLayer H 1) :=
  fun u ↦ Additive.ofMul
    (lowerCentralSquareMap H hSq (Additive.toMul u))

@[simp]
theorem lowerCentralSquareMapAdditive_mk
    (H : Type uH) [Group H]
    (hSq : LowerCentralSquaresLieInSecond H)
    (x : ↥(lowerCentralTerm H 0)) :
    lowerCentralSquareMapAdditive H hSq
        (Additive.ofMul
          (QuotientGroup.mk' (lowerCentralLayerKernel H 0) x)) =
      Additive.ofMul (lowerCentralSquareValue H hSq x) := by
  rfl

/-- **Higman Lemma 5**, quadratic add law. -/
theorem lowerCentralSquareMapAdditive_add
    (H : Type uH) [Group H]
    (hSq : LowerCentralSquaresLieInSecond H)
    (u v : Additive (lowerCentralLayer H 0)) :
    letI : IsMulCommutative (lowerCentralLayer H 0) :=
      lowerCentralLayerIsMulCommutative H 0
    letI : IsMulCommutative (lowerCentralLayer H 1) :=
      lowerCentralLayerIsMulCommutative H 1
    letI : Module (ZMod 2) (Additive (lowerCentralLayer H 0)) :=
      lowerCentralLayerZmodModule H 0
    letI : Module (ZMod 2) (Additive (lowerCentralLayer H 1)) :=
      lowerCentralLayerZmodModule H 1
    lowerCentralSquareMapAdditive H hSq (u + v) =
      lowerCentralSquareMapAdditive H hSq u +
        lowerCentralSquareMapAdditive H hSq v +
          lowerCentralCommutatorBilinear H u v := by
  letI : IsMulCommutative (lowerCentralLayer H 0) :=
    lowerCentralLayerIsMulCommutative H 0
  letI : IsMulCommutative (lowerCentralLayer H 1) :=
    lowerCentralLayerIsMulCommutative H 1
  letI : Module (ZMod 2) (Additive (lowerCentralLayer H 0)) :=
    lowerCentralLayerZmodModule H 0
  letI : Module (ZMod 2) (Additive (lowerCentralLayer H 1)) :=
    lowerCentralLayerZmodModule H 1
  simpa [lowerCentralSquareMapAdditive,
    lowerCentralCommutatorBilinear_apply] using
    congrArg Additive.ofMul
      (lowerCentralSquareMap_mul H hSq (Additive.toMul u) (Additive.toMul v))

/-- Higman's square map, bundled as a quadratic map over `F₂`. -/
noncomputable def lowerCentralSquareQuadraticMap
    (H : Type uH) [Group H]
    (hSq : LowerCentralSquaresLieInSecond H) :
    letI : IsMulCommutative (lowerCentralLayer H 0) :=
      lowerCentralLayerIsMulCommutative H 0
    letI : IsMulCommutative (lowerCentralLayer H 1) :=
      lowerCentralLayerIsMulCommutative H 1
    letI : Module (ZMod 2) (Additive (lowerCentralLayer H 0)) :=
      lowerCentralLayerZmodModule H 0
    letI : Module (ZMod 2) (Additive (lowerCentralLayer H 1)) :=
      lowerCentralLayerZmodModule H 1
    QuadraticMap (ZMod 2)
      (Additive (lowerCentralLayer H 0))
      (Additive (lowerCentralLayer H 1)) := by
  letI : IsMulCommutative (lowerCentralLayer H 0) :=
    lowerCentralLayerIsMulCommutative H 0
  letI : IsMulCommutative (lowerCentralLayer H 1) :=
    lowerCentralLayerIsMulCommutative H 1
  letI : Module (ZMod 2) (Additive (lowerCentralLayer H 0)) :=
    lowerCentralLayerZmodModule H 0
  letI : Module (ZMod 2) (Additive (lowerCentralLayer H 1)) :=
    lowerCentralLayerZmodModule H 1
  have hzero : lowerCentralSquareMapAdditive H hSq 0 = 0 := by
    have h := lowerCentralSquareMapAdditive_add H hSq
      (0 : Additive (lowerCentralLayer H 0)) 0
    have h' : lowerCentralSquareMapAdditive H hSq 0 + 0 =
        lowerCentralSquareMapAdditive H hSq 0 +
          lowerCentralSquareMapAdditive H hSq 0 := by
      simpa only [zero_add, map_zero, add_zero] using h
    exact (add_left_cancel h').symm
  refine
    { toFun := lowerCentralSquareMapAdditive H hSq
      toFun_smul := ?_
      exists_companion' := ⟨lowerCentralCommutatorBilinear H, ?_⟩ }
  · intro a u
    rcases (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) a with rfl | rfl
    · simpa using hzero
    · simp
  · exact lowerCentralSquareMapAdditive_add H hSq

/-- The polar form of Higman's square map is exactly the lower-central
commutator pairing. -/
theorem lowerCentralSquareQuadraticMap_polarBilin
    (H : Type uH) [Group H]
    (hSq : LowerCentralSquaresLieInSecond H) :
    letI : IsMulCommutative (lowerCentralLayer H 0) :=
      lowerCentralLayerIsMulCommutative H 0
    letI : IsMulCommutative (lowerCentralLayer H 1) :=
      lowerCentralLayerIsMulCommutative H 1
    letI : Module (ZMod 2) (Additive (lowerCentralLayer H 0)) :=
      lowerCentralLayerZmodModule H 0
    letI : Module (ZMod 2) (Additive (lowerCentralLayer H 1)) :=
      lowerCentralLayerZmodModule H 1
    (lowerCentralSquareQuadraticMap H hSq).polarBilin =
      lowerCentralCommutatorBilinear H := by
  letI : IsMulCommutative (lowerCentralLayer H 0) :=
    lowerCentralLayerIsMulCommutative H 0
  letI : IsMulCommutative (lowerCentralLayer H 1) :=
    lowerCentralLayerIsMulCommutative H 1
  letI : Module (ZMod 2) (Additive (lowerCentralLayer H 0)) :=
    lowerCentralLayerZmodModule H 0
  letI : Module (ZMod 2) (Additive (lowerCentralLayer H 1)) :=
    lowerCentralLayerZmodModule H 1
  apply LinearMap.ext
  intro u
  apply LinearMap.ext
  intro v
  rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar]
  change lowerCentralSquareMapAdditive H hSq (u + v) -
      lowerCentralSquareMapAdditive H hSq u -
        lowerCentralSquareMapAdditive H hSq v =
    lowerCentralCommutatorBilinear H u v
  rw [lowerCentralSquareMapAdditive_add]
  abel

/-- Squaring a transformed representative is the transform of its square. -/
theorem lowerCentralSquareRepresentative_equivariant
    {H : Type uH} {X : Type uMain} [Group H] [Group X]
    (phi : X →* MulAut H)
    (hSq : LowerCentralSquaresLieInSecond H)
    (g : X) (x : ↥(lowerCentralTerm H 0)) :
    lowerCentralSquareRepresentative H hSq
        (lowerCentralTermAction phi 0 g x) =
      lowerCentralTermAction phi 1 g
        (lowerCentralSquareRepresentative H hSq x) := by
  apply Subtype.ext
  change (phi g (x : H)) ^ 2 = phi g ((x : H) ^ 2)
  exact (map_pow (phi g) (x : H) 2).symm

/-- Equivariance after reducing representative squares modulo `H₂²H₃`. -/
theorem lowerCentralSquareValue_equivariant
    {H : Type uH} {X : Type uMain} [Group H] [Group X]
    (phi : X →* MulAut H)
    (hSq : LowerCentralSquaresLieInSecond H)
    (g : X) (x : ↥(lowerCentralTerm H 0)) :
    lowerCentralSquareValue H hSq
        (lowerCentralTermAction phi 0 g x) =
      lowerCentralLayerAction phi 1 g
        (lowerCentralSquareValue H hSq x) := by
  rw [lowerCentralSquareValue, lowerCentralSquareValue,
    lowerCentralLayerAction_apply_mk]
  exact congrArg (QuotientGroup.mk' (lowerCentralLayerKernel H 1))
    (lowerCentralSquareRepresentative_equivariant phi hSq g x)

/-- Equivariance of the descended multiplicative square map. -/
theorem lowerCentralSquareMap_equivariant
    {H : Type uH} {X : Type uMain} [Group H] [Group X]
    (phi : X →* MulAut H)
    (hSq : LowerCentralSquaresLieInSecond H)
    (g : X) (u : lowerCentralLayer H 0) :
    lowerCentralSquareMap H hSq (lowerCentralLayerAction phi 0 g u) =
      lowerCentralLayerAction phi 1 g (lowerCentralSquareMap H hSq u) := by
  obtain ⟨x, rfl⟩ :=
    QuotientGroup.mk'_surjective (lowerCentralLayerKernel H 0) u
  rw [lowerCentralLayerAction_apply_mk, lowerCentralSquareMap_mk,
    lowerCentralSquareMap_mk]
  exact lowerCentralSquareValue_equivariant phi hSq g x

/-- Higman's equation `(u ξ)⁽²⁾ = u⁽²⁾ ξ` in the canonical additive
`F₂` representations of the first two lower-central layers. -/
theorem lowerCentralSquareMapAdditive_equivariant
    {H : Type uH} {X : Type uMain} [Group H] [Group X]
    (phi : X →* MulAut H)
    (hSq : LowerCentralSquaresLieInSecond H)
    (g : X) (u : Additive (lowerCentralLayer H 0)) :
    letI : IsMulCommutative (lowerCentralLayer H 0) :=
      lowerCentralLayerIsMulCommutative H 0
    letI : IsMulCommutative (lowerCentralLayer H 1) :=
      lowerCentralLayerIsMulCommutative H 1
    letI : Module (ZMod 2) (Additive (lowerCentralLayer H 0)) :=
      lowerCentralLayerZmodModule H 0
    letI : Module (ZMod 2) (Additive (lowerCentralLayer H 1)) :=
      lowerCentralLayerZmodModule H 1
    lowerCentralSquareMapAdditive H hSq
        (lowerCentralLayerRepresentation phi 0 g u) =
      lowerCentralLayerRepresentation phi 1 g
        (lowerCentralSquareMapAdditive H hSq u) := by
  letI : IsMulCommutative (lowerCentralLayer H 0) :=
    lowerCentralLayerIsMulCommutative H 0
  letI : IsMulCommutative (lowerCentralLayer H 1) :=
    lowerCentralLayerIsMulCommutative H 1
  letI : Module (ZMod 2) (Additive (lowerCentralLayer H 0)) :=
    lowerCentralLayerZmodModule H 0
  letI : Module (ZMod 2) (Additive (lowerCentralLayer H 1)) :=
    lowerCentralLayerZmodModule H 1
  rw [show u = Additive.ofMul (Additive.toMul u) from rfl]
  rw [lowerCentralLayerRepresentation_apply]
  change Additive.ofMul
      (lowerCentralSquareMap H hSq
        (lowerCentralLayerAction phi 0 g (Additive.toMul u))) =
    lowerCentralLayerRepresentation phi 1 g
      (Additive.ofMul
        (lowerCentralSquareMap H hSq (Additive.toMul u)))
  rw [lowerCentralLayerRepresentation_apply]
  exact congrArg Additive.ofMul
    (lowerCentralSquareMap_equivariant phi hSq g (Additive.toMul u))

/-- The actual Higman square map, included into a scalar extension by
`v ↦ 1 ⊗ v`.  Only the codomain is extended, as in **Higman Lemma 5**. -/
noncomputable def lowerCentralSquareMapBaseChange
    (K : Type uK) [Field K] [Algebra (ZMod 2) K]
    (H : Type uH) [Group H]
    (hSq : LowerCentralSquaresLieInSecond H) :
    letI : IsMulCommutative (lowerCentralLayer H 0) :=
      lowerCentralLayerIsMulCommutative H 0
    letI : IsMulCommutative (lowerCentralLayer H 1) :=
      lowerCentralLayerIsMulCommutative H 1
    letI : Module (ZMod 2) (Additive (lowerCentralLayer H 0)) :=
      lowerCentralLayerZmodModule H 0
    letI : Module (ZMod 2) (Additive (lowerCentralLayer H 1)) :=
      lowerCentralLayerZmodModule H 1
    Additive (lowerCentralLayer H 0) →
      K ⊗[ZMod 2] Additive (lowerCentralLayer H 1) := by
  letI : IsMulCommutative (lowerCentralLayer H 0) :=
    lowerCentralLayerIsMulCommutative H 0
  letI : IsMulCommutative (lowerCentralLayer H 1) :=
    lowerCentralLayerIsMulCommutative H 1
  letI : Module (ZMod 2) (Additive (lowerCentralLayer H 0)) :=
    lowerCentralLayerZmodModule H 0
  letI : Module (ZMod 2) (Additive (lowerCentralLayer H 1)) :=
    lowerCentralLayerZmodModule H 1
  exact fun u ↦
    TensorProduct.mk (ZMod 2) K (Additive (lowerCentralLayer H 1)) 1
      (lowerCentralSquareMapAdditive H hSq u)

/-- The scalar-extension-valued square map has the actual commutator bracket,
included by `v ↦ 1 ⊗ v`, as its additive defect. -/
theorem lowerCentralSquareMapBaseChange_add
    (K : Type uK) [Field K] [Algebra (ZMod 2) K]
    (H : Type uH) [Group H]
    (hSq : LowerCentralSquaresLieInSecond H)
    (u v :
      letI : IsMulCommutative (lowerCentralLayer H 0) :=
        lowerCentralLayerIsMulCommutative H 0
      letI : Module (ZMod 2) (Additive (lowerCentralLayer H 0)) :=
        lowerCentralLayerZmodModule H 0
      Additive (lowerCentralLayer H 0)) :
    letI : IsMulCommutative (lowerCentralLayer H 0) :=
      lowerCentralLayerIsMulCommutative H 0
    letI : IsMulCommutative (lowerCentralLayer H 1) :=
      lowerCentralLayerIsMulCommutative H 1
    letI : Module (ZMod 2) (Additive (lowerCentralLayer H 0)) :=
      lowerCentralLayerZmodModule H 0
    letI : Module (ZMod 2) (Additive (lowerCentralLayer H 1)) :=
      lowerCentralLayerZmodModule H 1
    lowerCentralSquareMapBaseChange K H hSq (u + v) =
      lowerCentralSquareMapBaseChange K H hSq u +
        lowerCentralSquareMapBaseChange K H hSq v +
          TensorProduct.mk (ZMod 2) K
            (Additive (lowerCentralLayer H 1)) 1
            (lowerCentralCommutatorBilinear H u v) := by
  letI : IsMulCommutative (lowerCentralLayer H 0) :=
    lowerCentralLayerIsMulCommutative H 0
  letI : IsMulCommutative (lowerCentralLayer H 1) :=
    lowerCentralLayerIsMulCommutative H 1
  letI : Module (ZMod 2) (Additive (lowerCentralLayer H 0)) :=
    lowerCentralLayerZmodModule H 0
  letI : Module (ZMod 2) (Additive (lowerCentralLayer H 1)) :=
    lowerCentralLayerZmodModule H 1
  unfold lowerCentralSquareMapBaseChange
  simpa only [map_add] using congrArg
    (TensorProduct.mk (ZMod 2) K
      (Additive (lowerCentralLayer H 1)) 1)
    (lowerCentralSquareMapAdditive_add H hSq u v)

/-- Equivariance of the extension-valued actual square map. -/
theorem lowerCentralSquareMapBaseChange_equivariant
    (K : Type uK) [Field K] [Algebra (ZMod 2) K]
    {H : Type uH} {X : Type uMain} [Group H] [Group X]
    (phi : X →* MulAut H)
    (hSq : LowerCentralSquaresLieInSecond H)
    (g : X)
    (u :
      letI : IsMulCommutative (lowerCentralLayer H 0) :=
        lowerCentralLayerIsMulCommutative H 0
      letI : Module (ZMod 2) (Additive (lowerCentralLayer H 0)) :=
        lowerCentralLayerZmodModule H 0
      Additive (lowerCentralLayer H 0)) :
    letI : IsMulCommutative (lowerCentralLayer H 0) :=
      lowerCentralLayerIsMulCommutative H 0
    letI : IsMulCommutative (lowerCentralLayer H 1) :=
      lowerCentralLayerIsMulCommutative H 1
    letI : Module (ZMod 2) (Additive (lowerCentralLayer H 0)) :=
      lowerCentralLayerZmodModule H 0
    letI : Module (ZMod 2) (Additive (lowerCentralLayer H 1)) :=
      lowerCentralLayerZmodModule H 1
    lowerCentralSquareMapBaseChange K H hSq
        (lowerCentralLayerRepresentation phi 0 g u) =
      (lowerCentralLayerRepresentation phi 1 g).baseChange K
        (lowerCentralSquareMapBaseChange K H hSq u) := by
  letI : IsMulCommutative (lowerCentralLayer H 0) :=
    lowerCentralLayerIsMulCommutative H 0
  letI : IsMulCommutative (lowerCentralLayer H 1) :=
    lowerCentralLayerIsMulCommutative H 1
  letI : Module (ZMod 2) (Additive (lowerCentralLayer H 0)) :=
    lowerCentralLayerZmodModule H 0
  letI : Module (ZMod 2) (Additive (lowerCentralLayer H 1)) :=
    lowerCentralLayerZmodModule H 1
  unfold lowerCentralSquareMapBaseChange
  rw [lowerCentralSquareMapAdditive_equivariant phi hSq g u]
  exact (LinearMap.baseChange_tmul
    (lowerCentralLayerRepresentation phi 1 g) (A := K) 1
    (lowerCentralSquareMapAdditive H hSq u)).symm

/-! ## The upper-triangular candidate for Higman's coordinate formula -/

section UpperTriangularQuadratic

universe uR uM uN

variable {R : Type uR} {M : Type uM} {N : Type uN}
variable [CommRing R] [AddCommGroup M] [AddCommGroup N]
variable [Module R M] [Module R N]

/-- The upper-triangular bilinear companion attached to a bilinear map and an
ordered basis. -/
noncomputable def upperCompanion {m : ℕ} (b : Basis (Fin m) R M)
    (beta : LinearMap.BilinMap R M N) : LinearMap.BilinMap R M N :=
  b.constr (S := R) fun i ↦
    b.constr (S := R) fun j ↦
      if i < j then beta (b i) (b j) else 0

@[simp]
theorem upperCompanion_apply_basis {m : ℕ} (b : Basis (Fin m) R M)
    (beta : LinearMap.BilinMap R M N) (i j : Fin m) :
    upperCompanion b beta (b i) (b j) =
      if i < j then beta (b i) (b j) else 0 := by
  rw [upperCompanion, b.constr_basis]
  exact b.constr_basis R _ j

/-- The quadratic map whose chosen companion is the upper-triangular half
of `beta`. -/
noncomputable def upperQuadraticMap {m : ℕ} (b : Basis (Fin m) R M)
    (beta : LinearMap.BilinMap R M N) : QuadraticMap R M N :=
  (upperCompanion b beta).toQuadraticMap

/-- Evaluation of the upper-triangular candidate in basis coordinates. -/
theorem upperQuadraticMap_apply_sum {m : ℕ} (b : Basis (Fin m) R M)
    (beta : LinearMap.BilinMap R M N) (a : Fin m → R) :
    upperQuadraticMap b beta (∑ i, a i • b i) =
      ∑ i, ∑ j with i < j, (a i * a j) • beta (b i) (b j) := by
  simp only [upperQuadraticMap, LinearMap.BilinMap.toQuadraticMap_apply]
  simp_rw [LinearMap.map_sum₂, map_sum, LinearMap.map_smul₂, map_smul,
    upperCompanion_apply_basis, smul_ite, smul_zero, mul_smul]
  simp only [Finset.sum_filter]

/-- The coordinate template for **Higman Lemma 5** (p. 85). On
Frobenius-power coordinates, the upper-triangular candidate has Higman's
pairwise-exponent polynomial. This theorem does not yet identify the candidate
with `lowerCentralSquareMapBaseChange`. -/
theorem upperQuadraticMap_apply_frobenius_sum {m : ℕ}
    (b : Basis (Fin m) R M) (beta : LinearMap.BilinMap R M N) (alpha : R) :
    upperQuadraticMap b beta
        (∑ i : Fin m, alpha ^ (2 ^ (i : ℕ)) • b i) =
      ∑ i : Fin m, ∑ j : Fin m with i < j,
        alpha ^ (2 ^ (i : ℕ) + 2 ^ (j : ℕ)) • beta (b i) (b j) := by
  simpa only [pow_add] using
    (upperQuadraticMap_apply_sum b beta
      (fun i ↦ alpha ^ (2 ^ (i : ℕ))))

/-- In characteristic two, the polar form of the constructed quadratic map
is the original alternating bilinear map. -/
theorem polarBilin_upperQuadraticMap {m : ℕ} [CharP R 2]
    (b : Basis (Fin m) R M) (beta : LinearMap.BilinMap R M N)
    (hbeta : beta.IsAlt) :
    QuadraticMap.polarBilin (upperQuadraticMap b beta) = beta := by
  rw [upperQuadraticMap, LinearMap.BilinMap.polarBilin_toQuadraticMap]
  apply b.ext
  intro i
  apply b.ext
  intro j
  simp only [LinearMap.add_apply, LinearMap.flip_apply,
    upperCompanion_apply_basis]
  obtain hij | rfl | hji := lt_trichotomy i j
  · simp [hij, hij.not_gt]
  · simpa using (hbeta.self_eq_zero (b i)).symm
  · have hneg : -(beta (b j) (b i)) = beta (b j) (b i) := by
      rw [neg_eq_iff_add_eq_zero, ← two_smul R]
      rw [show (2 : R) = 0 from CharP.cast_eq_zero R 2, zero_smul]
    simpa [hji, hji.not_gt, hneg] using hbeta.neg (b j) (b i)

/-- An upper-triangular quadratic map is equivariant when its ordered basis
consists of weight vectors and its bilinear input is equivariant. -/
theorem upperQuadraticMap_equivariant_of_eigenbasis
    {K : Type uR} {V : Type uM} {W : Type uN}
    [Field K]
    [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W]
    {m : ℕ}
    (b : Basis (Fin m) K V)
    (T₁ : Module.End K V) (T₂ : Module.End K W)
    (weight : Fin m → K)
    (hb : ∀ i, T₁ (b i) = weight i • b i)
    (beta : LinearMap.BilinMap K V W)
    (hbeta : ∀ x y, T₂ (beta x y) = beta (T₁ x) (T₁ y))
    (x : V) :
    upperQuadraticMap b beta (T₁ x) =
      T₂ (upperQuadraticMap b beta x) := by
  let a : Fin m → K := fun i ↦ b.repr x i
  have hx : x = ∑ i, a i • b i := (b.sum_repr x).symm
  rw [hx]
  have hT₁ : T₁ (∑ i, a i • b i) =
      ∑ i, (a i * weight i) • b i := by
    simp_rw [map_sum, map_smul, hb, smul_smul]
  rw [hT₁, upperQuadraticMap_apply_sum,
    upperQuadraticMap_apply_sum]
  simp_rw [map_sum, map_smul, hbeta, hb,
    LinearMap.map_smul₂, map_smul, smul_smul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  ring

end UpperTriangularQuadratic

/-! ## The uniqueness argument in Higman Lemma 5 -/

/-- Two equivariant maps with the same additive defect agree when the source
representation is irreducible and the target scalar extension contains no
injective copy of it.  This is the uniqueness argument in **Higman Lemma 5**
(p. 85): the difference is an equivariant `F₂`-linear map, hence is either
zero or injective. -/
theorem eq_of_same_add_law_and_equivariant_of_no_injective_intertwiner
    {K : Type uK} {C V₁ V₂ : Type uMain}
    [Field K] [Algebra (ZMod 2) K]
    [Group C]
    [AddCommGroup V₁] [Module (ZMod 2) V₁]
    [AddCommGroup V₂] [Module (ZMod 2) V₂]
    (rho₁ : Representation (ZMod 2) C V₁)
    (rho₂ : Representation (ZMod 2) C V₂)
    (hirr₁ : Representation.IsIrreducible rho₁)
    (polar : V₁ → V₁ → K ⊗[ZMod 2] V₂)
    (q q' : V₁ → K ⊗[ZMod 2] V₂)
    (hq_add : ∀ x y, q (x + y) = q x + q y + polar x y)
    (hq'_add : ∀ x y, q' (x + y) = q' x + q' y + polar x y)
    (hq_equiv : ∀ c x, q (rho₁ c x) = (rho₂ c).baseChange K (q x))
    (hq'_equiv : ∀ c x, q' (rho₁ c x) = (rho₂ c).baseChange K (q' x))
    (hno : ¬ ∃ f : V₁ →ₗ[ZMod 2] K ⊗[ZMod 2] V₂,
      Function.Injective f ∧
      ∀ c v, f (rho₁ c v) = (rho₂ c).baseChange K (f v)) :
    q = q' := by
  let dAdd : V₁ →+ K ⊗[ZMod 2] V₂ :=
    AddMonoidHom.mk' (fun v ↦ q v - q' v) (by
      intro x y
      rw [hq_add, hq'_add]
      abel)
  let d : V₁ →ₗ[ZMod 2] K ⊗[ZMod 2] V₂ := dAdd.toZModLinearMap 2
  have hd_apply (v : V₁) : d v = q v - q' v := rfl
  have hinter : ∀ c v, d (rho₁ c v) = (rho₂ c).baseChange K (d v) := by
    intro c v
    rw [hd_apply, hd_apply, hq_equiv, hq'_equiv, map_sub]
  let S : Subrepresentation rho₁ := {
    toSubmodule := LinearMap.ker d
    apply_mem_toSubmodule := by
      intro c v hv
      change d (rho₁ c v) = 0
      change d v = 0 at hv
      rw [hinter, hv, map_zero] }
  letI : Representation.IsIrreducible rho₁ := hirr₁
  rcases eq_bot_or_eq_top S with hS | hS
  · exfalso
    apply hno
    refine ⟨d, ?_, hinter⟩
    apply LinearMap.ker_eq_bot.mp
    exact congrArg Subrepresentation.toSubmodule hS
  · have hd_zero : d = 0 := LinearMap.ker_eq_top.mp <|
      congrArg Subrepresentation.toSubmodule hS
    funext v
    apply sub_eq_zero.mp
    rw [← hd_apply]
    simp [hd_zero]

/-- **Higman Lemma 5** (uniqueness, p. 85), in the faithful cyclic-actor
specialization used by the formalized Lemma 4. The quadratic add law and
equivariance characterize a map from the first layer to the scalar extension
of the second layer. -/
theorem eq_of_same_add_law_and_equivariant_of_higman_bracket
    {K : Type uK} {C V₁ V₂ : Type uMain}
    [Field K] [Algebra (ZMod 2) K]
    [CommGroup C] [IsCyclic C] [Finite C]
    [AddCommGroup V₁] [Module (ZMod 2) V₁] [Finite V₁]
    [AddCommGroup V₂] [Module (ZMod 2) V₂] [Finite V₂]
    (rho₁ : Representation (ZMod 2) C V₁)
    (rho₂ : Representation (ZMod 2) C V₂)
    (n : ℕ) (hn : 2 ≤ n)
    (hfin₂ : Module.finrank (ZMod 2) V₂ = n)
    (hirr₁ : Representation.IsIrreducible rho₁)
    (hfaith₁ : Function.Injective rho₁)
    (beta : LinearMap.BilinMap (ZMod 2) V₁ V₂)
    (hbetaEquiv : ∀ c x y,
      rho₂ c (beta x y) = beta (rho₁ c x) (rho₁ c y))
    (hbetaAlt : ∀ x, beta x x = 0)
    (hbetaSpan : Submodule.span (ZMod 2)
      (Set.range fun z : V₁ × V₁ ↦ beta z.1 z.2) = ⊤)
    (htrans₂ : ∀ v w : V₂, v ≠ 0 → w ≠ 0 →
      ∃ c : C, rho₂ c v = w)
    (polar : V₁ → V₁ → K ⊗[ZMod 2] V₂)
    (q q' : V₁ → K ⊗[ZMod 2] V₂)
    (hq_add : ∀ x y, q (x + y) = q x + q y + polar x y)
    (hq'_add : ∀ x y, q' (x + y) = q' x + q' y + polar x y)
    (hq_equiv : ∀ c x, q (rho₁ c x) = (rho₂ c).baseChange K (q x))
    (hq'_equiv : ∀ c x, q' (rho₁ c x) = (rho₂ c).baseChange K (q' x)) :
    q = q' :=
  eq_of_same_add_law_and_equivariant_of_no_injective_intertwiner
    rho₁ rho₂ hirr₁ polar q q' hq_add hq'_add hq_equiv hq'_equiv
    (not_exists_injective_intertwiner_to_baseChange_of_higman_bracket
      rho₁ rho₂ n hn hfin₂ hirr₁ hfaith₁ beta hbetaEquiv hbetaAlt
      hbetaSpan htrans₂)

section ActualUniqueness

variable {H : Type uH} [Group H]

local instance instActualUniquenessLayerIsMulCommutative (i : ℕ) :
    IsMulCommutative (lowerCentralLayer H i) :=
  lowerCentralLayerIsMulCommutative H i

noncomputable local instance instActualUniquenessLayerZModTwoModule (i : ℕ) :
    Module (ZMod 2) (Additive (lowerCentralLayer H i)) :=
  lowerCentralLayerZmodModule H i

/-- **Higman Lemma 5** (source-facing uniqueness, p. 85), in the faithful
cyclic-actor specialization used by the formalized Lemma 4. For the actual
lower-central square and commutator maps, the quadratic add law and
equivariance characterize the map after every scalar extension. -/
theorem lowerCentralSquareMapBaseChange_eq_of_add_law_and_equivariant
    (K : Type uK) [Field K] [Algebra (ZMod 2) K]
    {C : Type uH} [CommGroup C] [IsCyclic C] [Finite C] [Finite H]
    (phi : C →* MulAut H)
    (hSq : LowerCentralSquaresLieInSecond H)
    (n : ℕ) (hn : 2 ≤ n)
    (hfin₂ : Module.finrank (ZMod 2)
      (Additive (lowerCentralLayer H 1)) = n)
    (hirr₁ : Representation.IsIrreducible
      (lowerCentralLayerRepresentation phi 0))
    (hfaith₁ : Function.Injective
      (lowerCentralLayerRepresentation phi 0))
    (htrans₂ : ∀ v w : Additive (lowerCentralLayer H 1),
      v ≠ 0 → w ≠ 0 → ∃ c : C,
        lowerCentralLayerRepresentation phi 1 c v = w)
    (q' : Additive (lowerCentralLayer H 0) →
      K ⊗[ZMod 2] Additive (lowerCentralLayer H 1))
    (hq'_add : ∀ x y,
      q' (x + y) = q' x + q' y +
        TensorProduct.mk (ZMod 2) K
          (Additive (lowerCentralLayer H 1)) 1
          (lowerCentralCommutatorBilinear H x y))
    (hq'_equiv : ∀ c x,
      q' (lowerCentralLayerRepresentation phi 0 c x) =
        (lowerCentralLayerRepresentation phi 1 c).baseChange K (q' x)) :
    lowerCentralSquareMapBaseChange K H hSq = q' := by
  let polar : Additive (lowerCentralLayer H 0) →
      Additive (lowerCentralLayer H 0) →
        K ⊗[ZMod 2] Additive (lowerCentralLayer H 1) :=
    fun x y ↦
      TensorProduct.mk (ZMod 2) K
        (Additive (lowerCentralLayer H 1)) 1
        (lowerCentralCommutatorBilinear H x y)
  have hbetaEquiv : ∀ c x y,
      lowerCentralLayerRepresentation phi 1 c
          (lowerCentralCommutatorBilinear H x y) =
        lowerCentralCommutatorBilinear H
          (lowerCentralLayerRepresentation phi 0 c x)
          (lowerCentralLayerRepresentation phi 0 c y) := by
    intro c x y
    simpa only [← lowerCentralLayerRepresentation_apply, ofMul_toMul] using
      lowerCentralCommutatorBilinear_equivariant phi c x y
  have hq_add : ∀ x y,
      lowerCentralSquareMapBaseChange K H hSq (x + y) =
        lowerCentralSquareMapBaseChange K H hSq x +
          lowerCentralSquareMapBaseChange K H hSq y + polar x y := by
    intro x y
    simpa only [polar] using
      lowerCentralSquareMapBaseChange_add K H hSq x y
  have hq_equiv : ∀ c x,
      lowerCentralSquareMapBaseChange K H hSq
          (lowerCentralLayerRepresentation phi 0 c x) =
        (lowerCentralLayerRepresentation phi 1 c).baseChange K
          (lowerCentralSquareMapBaseChange K H hSq x) := by
    intro c x
    exact lowerCentralSquareMapBaseChange_equivariant K phi hSq c x
  exact eq_of_same_add_law_and_equivariant_of_higman_bracket
    (lowerCentralLayerRepresentation phi 0)
    (lowerCentralLayerRepresentation phi 1)
    n hn hfin₂ hirr₁ hfaith₁
    (lowerCentralCommutatorBilinear H)
    hbetaEquiv
    (lowerCentralCommutatorBilinear_self H)
    (lowerCentralCommutatorBilinear_span_eq_top H)
    htrans₂ polar
    (lowerCentralSquareMapBaseChange K H hSq) q'
    hq_add (by simpa only [polar] using hq'_add)
    hq_equiv hq'_equiv

end ActualUniqueness

/-! ## Identification with the upper-triangular candidate -/

section ActualCandidate

variable {H : Type uH} [Group H]

local instance instActualCandidateLayerIsMulCommutative (i : ℕ) :
    IsMulCommutative (lowerCentralLayer H i) :=
  lowerCentralLayerIsMulCommutative H i

noncomputable local instance instActualCandidateLayerZModTwoModule (i : ℕ) :
    Module (ZMod 2) (Additive (lowerCentralLayer H i)) :=
  lowerCentralLayerZmodModule H i

/-- The upper-triangular coordinate candidate, restricted along the canonical
map `x ↦ 1 ⊗ x` from the actual first lower-central layer. -/
noncomputable def lowerCentralUpperQuadraticCandidate
    (K : Type uK) [Field K] [Algebra (ZMod 2) K]
    {m : ℕ}
    (b : Basis (Fin m) K
      (K ⊗[ZMod 2] Additive (lowerCentralLayer H 0))) :
    Additive (lowerCentralLayer H 0) →
      K ⊗[ZMod 2] Additive (lowerCentralLayer H 1) :=
  fun x ↦ upperQuadraticMap b
    (lowerCentralCommutatorBilinearBaseChange K H)
    (1 ⊗ₜ[ZMod 2] x)

/-- The candidate has the actual lower-central commutator as its additive
defect. -/
theorem lowerCentralUpperQuadraticCandidate_add
    (K : Type uK) [Field K] [Algebra (ZMod 2) K]
    {m : ℕ}
    (b : Basis (Fin m) K
      (K ⊗[ZMod 2] Additive (lowerCentralLayer H 0)))
    (x y : Additive (lowerCentralLayer H 0)) :
    lowerCentralUpperQuadraticCandidate K b (x + y) =
      lowerCentralUpperQuadraticCandidate K b x +
        lowerCentralUpperQuadraticCandidate K b y +
          TensorProduct.mk (ZMod 2) K
            (Additive (lowerCentralLayer H 1)) 1
            (lowerCentralCommutatorBilinear H x y) := by
  letI : CharP K 2 :=
    charP_of_injective_algebraMap
      (algebraMap (ZMod 2) K).injective 2
  let beta := lowerCentralCommutatorBilinearBaseChange K H
  let Q := upperQuadraticMap b beta
  have hAlt : beta.IsAlt := fun u ↦
    lowerCentralCommutatorBilinearBaseChange_self K H u
  have hpolar : QuadraticMap.polarBilin Q = beta := by
    exact polarBilin_upperQuadraticMap b beta hAlt
  change Q (1 ⊗ₜ[ZMod 2] (x + y)) =
    Q (1 ⊗ₜ[ZMod 2] x) + Q (1 ⊗ₜ[ZMod 2] y) + _
  rw [TensorProduct.tmul_add,
    QuadraticMap.map_add Q
      (1 ⊗ₜ[ZMod 2] x) (1 ⊗ₜ[ZMod 2] y),
    ← QuadraticMap.polarBilin_apply_apply, hpolar]
  simp [beta, lowerCentralCommutatorBilinearBaseChange]

/-- A weight basis makes the upper-triangular candidate equivariant for the
actual lower-central actions. -/
theorem lowerCentralUpperQuadraticCandidate_equivariant
    (K : Type uK) [Field K] [Algebra (ZMod 2) K]
    {C : Type uH} [Group C]
    (phi : C →* MulAut H)
    {m : ℕ}
    (b : Basis (Fin m) K
      (K ⊗[ZMod 2] Additive (lowerCentralLayer H 0)))
    (weight : C → Fin m → K)
    (hb : ∀ c i,
      (lowerCentralLayerRepresentation phi 0 c).baseChange K (b i) =
        weight c i • b i)
    (c : C) (x : Additive (lowerCentralLayer H 0)) :
    lowerCentralUpperQuadraticCandidate K b
        (lowerCentralLayerRepresentation phi 0 c x) =
      (lowerCentralLayerRepresentation phi 1 c).baseChange K
        (lowerCentralUpperQuadraticCandidate K b x) := by
  have h := upperQuadraticMap_equivariant_of_eigenbasis
    b
    ((lowerCentralLayerRepresentation phi 0 c).baseChange K)
    ((lowerCentralLayerRepresentation phi 1 c).baseChange K)
    (weight c) (hb c)
    (lowerCentralCommutatorBilinearBaseChange K H)
    (lowerCentralCommutatorBilinearBaseChange_equivariant K phi c)
    (1 ⊗ₜ[ZMod 2] x)
  simpa [lowerCentralUpperQuadraticCandidate] using h

/-- The actual lower-central square map is the upper-triangular coordinate
candidate once a simultaneous weight basis is supplied. -/
theorem lowerCentralSquareMapBaseChange_eq_upperQuadraticCandidate
    (K : Type uK) [Field K] [Algebra (ZMod 2) K]
    {C : Type uH}
    [CommGroup C] [IsCyclic C] [Finite C] [Finite H]
    (phi : C →* MulAut H)
    (hSq : LowerCentralSquaresLieInSecond H)
    (n : ℕ) (hn : 2 ≤ n)
    (hfin₂ : Module.finrank (ZMod 2)
      (Additive (lowerCentralLayer H 1)) = n)
    (hirr₁ : Representation.IsIrreducible
      (lowerCentralLayerRepresentation phi 0))
    (hfaith₁ : Function.Injective
      (lowerCentralLayerRepresentation phi 0))
    (htrans₂ : ∀ v w : Additive (lowerCentralLayer H 1),
      v ≠ 0 → w ≠ 0 → ∃ c : C,
        lowerCentralLayerRepresentation phi 1 c v = w)
    {m : ℕ}
    (b : Basis (Fin m) K
      (K ⊗[ZMod 2] Additive (lowerCentralLayer H 0)))
    (weight : C → Fin m → K)
    (hb : ∀ c i,
      (lowerCentralLayerRepresentation phi 0 c).baseChange K (b i) =
        weight c i • b i) :
    lowerCentralSquareMapBaseChange K H hSq =
      lowerCentralUpperQuadraticCandidate K b := by
  apply lowerCentralSquareMapBaseChange_eq_of_add_law_and_equivariant
    K phi hSq n hn hfin₂ hirr₁ hfaith₁ htrans₂
    (lowerCentralUpperQuadraticCandidate K b)
  · exact lowerCentralUpperQuadraticCandidate_add K b
  · exact lowerCentralUpperQuadraticCandidate_equivariant
      K phi b weight hb

end ActualCandidate

/-! ## Higman's Frobenius-coordinate formula -/

section FrobeniusFormula

variable {H C : Type uH} [Group H] [Finite H]
variable [CommGroup C] [IsCyclic C] [Finite C]

local instance higmanFormulaLayerIsMulCommutative (i : ℕ) :
    IsMulCommutative (lowerCentralLayer H i) :=
  lowerCentralLayerIsMulCommutative H i

noncomputable local instance higmanFormulaLayerZModTwoModule (i : ℕ) :
    Module (ZMod 2) (Additive (lowerCentralLayer H i)) :=
  lowerCentralLayerZmodModule H i

/-- **Higman Lemma 5** (p. 85), in the faithful cyclic-actor specialization
used here.  There is a normalized Frobenius-conjugate eigenbasis in which the
actual lower-central square map has Higman's displayed pairwise formula. -/
theorem exists_lowerCentralSquareMap_eq_frobeniusSum
    (phi : C →* MulAut H)
    (hAgemo : Agemo H 2 1 = lowerCentralTerm H 1)
    (m : ℕ) (hm : m ≠ 0)
    (hfin₁ : Module.finrank (ZMod 2)
      (Additive (lowerCentralLayer H 0)) = m)
    (n : ℕ) (hn : 2 ≤ n)
    (hfin₂ : Module.finrank (ZMod 2)
      (Additive (lowerCentralLayer H 1)) = n)
    (hirr₁ : Representation.IsIrreducible
      (lowerCentralLayerRepresentation phi 0))
    (hfaith₁ : Function.Injective
      (lowerCentralLayerRepresentation phi 0))
    (htrans₂ : ∀ v w : Additive (lowerCentralLayer H 1),
      v ≠ 0 → w ≠ 0 → ∃ c : C,
        lowerCentralLayerRepresentation phi 1 c v = w) :
    let K := GaloisField 2 m
    let hSq := lowerCentralSquaresLieInSecond_of_agemo_eq H hAgemo
    ∃ (e : Additive (lowerCentralLayer H 0) ≃ₗ[ZMod 2] K)
      (mu : C →* Kˣ)
      (b : Basis (Fin (Module.finrank (ZMod 2) K)) K
        (K ⊗[ZMod 2] Additive (lowerCentralLayer H 0))),
      Function.Injective mu ∧
      (∀ c x, e (lowerCentralLayerRepresentation phi 0 c x) =
        (mu c : K) * e x) ∧
      (∀ x, (1 : K) ⊗ₜ[ZMod 2] x =
        ∑ i : Fin (Module.finrank (ZMod 2) K),
          (e x) ^ (2 ^ i.val) • b i) ∧
      (∀ c i,
        (lowerCentralLayerRepresentation phi 0 c).baseChange K (b i) =
          ((mu c : K) ^ (2 ^ i.val)) • b i) ∧
      ∀ x,
        lowerCentralSquareMapBaseChange K H hSq x =
          ∑ i : Fin (Module.finrank (ZMod 2) K),
            ∑ j : Fin (Module.finrank (ZMod 2) K) with i < j,
              (e x) ^ (2 ^ i.val + 2 ^ j.val) •
                lowerCentralCommutatorBilinearBaseChange K H (b i) (b j) := by
  let K := GaloisField 2 m
  let hSq := lowerCentralSquaresLieInSecond_of_agemo_eq H hAgemo
  obtain ⟨e, mu, b, hmu, _hbdef, hcoord, hexpand, hb⟩ :=
    OddOrder.RepresentationTheory.exists_singerConjugateBasis_of_faithful_irreducible
      (lowerCentralLayerRepresentation phi 0) m hm hfin₁ hirr₁ hfaith₁
  refine ⟨e, mu, b, hmu, hcoord, hexpand, hb, ?_⟩
  intro x
  let weight : C → Fin (Module.finrank (ZMod 2) K) → K :=
    fun c i ↦ (mu c : K) ^ (2 ^ i.val)
  have hActual :
      lowerCentralSquareMapBaseChange K H hSq =
        lowerCentralUpperQuadraticCandidate K b := by
    exact lowerCentralSquareMapBaseChange_eq_upperQuadraticCandidate
      K phi hSq n hn hfin₂ hirr₁ hfaith₁ htrans₂ b weight hb
  calc
    lowerCentralSquareMapBaseChange K H hSq x =
        lowerCentralUpperQuadraticCandidate K b x :=
      congrFun hActual x
    _ = upperQuadraticMap b
          (lowerCentralCommutatorBilinearBaseChange K H)
          (∑ i : Fin (Module.finrank (ZMod 2) K),
            (e x) ^ (2 ^ i.val) • b i) := by
      simp only [lowerCentralUpperQuadraticCandidate]
      rw [← hexpand x]
    _ = ∑ i : Fin (Module.finrank (ZMod 2) K),
          ∑ j : Fin (Module.finrank (ZMod 2) K) with i < j,
            (e x) ^ (2 ^ i.val + 2 ^ j.val) •
              lowerCentralCommutatorBilinearBaseChange K H (b i) (b j) :=
      upperQuadraticMap_apply_frobenius_sum b
        (lowerCentralCommutatorBilinearBaseChange K H) (e x)

end FrobeniusFormula

end OddOrder.Higman.Suzuki2Groups
