/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.FieldTheory.Finite.Basic
import OddOrder.Peterfalvi.Appendices.Suzuki2Groups.Types

/-!
# Higman's Suzuki 2-group types C and D

G. Higman, *Suzuki 2-groups* (Illinois J. Math. 7, 1963), p. 81 (definition
table) and pp. 91--92 (classification proof).

Higman's Lemma 12 classifies every Suzuki `2`-group of `ξ`-length `3` as one of
`B(n, θ, ε)`, `C(n, ε)`, or `D(n, θ, ε)`.  The type-`B` model already lives in
`OddOrder.Peterfalvi.Appendices.Suzuki2Groups.Types` (Peterfalvi reproduces it
as Appendix III, Definition 3, because his development only needs type `B`).
Types `C` and `D` are Higman-specific, so this file — in Higman's own
territory — supplies their concrete quadratic-map models and honest data
carriers, matching the definition table on p. 81:

* `C(n, ε)`: `(α, β)² = α^{θ+1} + ε·α^{1/2}·β^{2θ} + β²`, with `2θ² = 1`;
* `D(n, θ, ε)`: `(α, β)² = α^{θ+1} + ε·α^{θ³}·β^θ + β^{θ²+1}`, with `θ⁵ = 1`,
  `θ ≠ 1`.

Here `α^{1/2}` is the inverse Frobenius (the square root in characteristic two)
and `α^θ = θ(α)`; the exponent `2θ` is the automorphism `α ↦ θ(α)²`.  As with
types `A` and `B`, the square map is built as an actual
`QuadraticMap (ZMod 2) (F × F) F`, so `TypeCData P` and `TypeDData P` carry
genuine group equivalences rather than proposition-valued labels.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

open OddOrder.Peterfalvi.Appendices.Suzuki2Groups

noncomputable section

universe uP uF

section TypeModels

variable {F : Type uF} [Field F] [Finite F] [CharP F 2]

-- Named to avoid a cross-file clash with the identically-shaped anonymous
-- `local instance` in `HigmanLemmaTwelve.LengthTwoModels` (same namespace).
local instance instAlgebraZMod2TypeModelsCD : Algebra (ZMod 2) F :=
  ZMod.algebra F 2

/-! ## Type C -/

/-- **Higman p. 81, type `C`.**  The quadratic map defining `C(n, ε)`,

`(α, β) ↦ α·θ(α) + ε·(α^{1/2}·(2θ)(β)) + β²`,

where `α^{1/2}` is the inverse Frobenius and `(2θ)(β) = θ(β)²`.  The intended
`θ` satisfies `2θ² = 1`, but the map itself is defined for every automorphism.
-/
def typeCQuadraticMap (theta : RingAut F) (epsilon : F) :
    QuadraticMap (ZMod 2) (F × F) F :=
  QuadraticMap.linMulLin
      (LinearMap.fst (ZMod 2) F F)
      ((ringAutToZModLinear theta).comp (LinearMap.fst (ZMod 2) F F)) +
    epsilon • QuadraticMap.linMulLin
      ((ringAutToZModLinear (frobeniusEquiv F 2)⁻¹).comp
        (LinearMap.fst (ZMod 2) F F))
      ((ringAutToZModLinear (frobeniusEquiv F 2 * theta)).comp
        (LinearMap.snd (ZMod 2) F F)) +
    QuadraticMap.linMulLin
      (LinearMap.snd (ZMod 2) F F)
      (LinearMap.snd (ZMod 2) F F)

@[simp]
theorem typeCQuadraticMap_apply (theta : RingAut F) (epsilon : F) (x : F × F) :
    typeCQuadraticMap theta epsilon x =
      x.1 * theta x.1 +
        epsilon *
          ((frobeniusEquiv F 2)⁻¹ x.1 * (frobeniusEquiv F 2 * theta) x.2) +
        x.2 * x.2 := by
  simp [typeCQuadraticMap]

/-- Higman's condition on `ε` for type `C`: the defining quadratic map has no
nonzero isotropic vector with both coordinates nonzero. -/
def IsTypeCEpsilon (theta : RingAut F) (epsilon : F) : Prop :=
  ∀ a b : F, a ≠ 0 → b ≠ 0 →
    a * theta a +
      epsilon * ((frobeniusEquiv F 2)⁻¹ a * (frobeniusEquiv F 2 * theta) b) +
      b * b ≠ 0

/-- Higman's condition on `ε` makes the type-`C` defining map anisotropic. -/
theorem typeCQuadraticMap_anisotropic (theta : RingAut F) (epsilon : F)
    (hε : IsTypeCEpsilon theta epsilon) :
    (typeCQuadraticMap theta epsilon).Anisotropic := by
  rintro ⟨a, b⟩ hq
  simp only [typeCQuadraticMap_apply] at hq
  by_cases ha : a = 0
  · subst a
    have hb : b = 0 := by simpa using hq
    subst b
    rfl
  by_cases hb : b = 0
  · subst b
    have ha0 : a = 0 := by simpa using hq
    exact (ha ha0).elim
  exact (hε a b ha hb hq).elim

/-- Higman's concrete group `C(n, ε)` as the quadratic central extension of the
map in the type-`C` row of the p. 81 table. -/
abbrev TypeCModel (theta : RingAut F) (epsilon : F) :=
  QuadraticExtension (typeCQuadraticMap theta epsilon)
    (Module.finBasis (ZMod 2) (F × F))

namespace TypeCModel

/-- Squaring in `C(n, ε)` is the type-`C` quadratic map. -/
theorem sq_eq_inl_quadraticMap (theta : RingAut F) (epsilon : F)
    (x : TypeCModel theta epsilon) :
    x ^ 2 =
      (QuadraticExtension.extension
        (typeCQuadraticMap theta epsilon)
        (Module.finBasis (ZMod 2) (F × F))).inl
          (Multiplicative.ofAdd
            (x.quotient.1 * theta x.quotient.1 +
              epsilon * ((frobeniusEquiv F 2)⁻¹ x.quotient.1 *
                (frobeniusEquiv F 2 * theta) x.quotient.2) +
              x.quotient.2 * x.quotient.2)) := by
  simpa only [typeCQuadraticMap_apply] using
    QuadraticExtension.sq_eq_inl_q
      (typeCQuadraticMap theta epsilon)
      (Module.finBasis (ZMod 2) (F × F)) x

end TypeCModel

/-! ## Type D -/

/-- **Higman p. 81, type `D`.**  The quadratic map defining `D(n, θ, ε)`,

`(α, β) ↦ α·θ(α) + ε·(θ³(α)·θ(β)) + β·θ²(β)`.

The intended `θ` satisfies `θ⁵ = 1`, `θ ≠ 1`, but the map is defined for every
automorphism. -/
def typeDQuadraticMap (theta : RingAut F) (epsilon : F) :
    QuadraticMap (ZMod 2) (F × F) F :=
  QuadraticMap.linMulLin
      (LinearMap.fst (ZMod 2) F F)
      ((ringAutToZModLinear theta).comp (LinearMap.fst (ZMod 2) F F)) +
    epsilon • QuadraticMap.linMulLin
      ((ringAutToZModLinear (theta ^ 3)).comp (LinearMap.fst (ZMod 2) F F))
      ((ringAutToZModLinear theta).comp (LinearMap.snd (ZMod 2) F F)) +
    QuadraticMap.linMulLin
      (LinearMap.snd (ZMod 2) F F)
      ((ringAutToZModLinear (theta ^ 2)).comp (LinearMap.snd (ZMod 2) F F))

omit [Finite F] in
@[simp]
theorem typeDQuadraticMap_apply (theta : RingAut F) (epsilon : F) (x : F × F) :
    typeDQuadraticMap theta epsilon x =
      x.1 * theta x.1 +
        epsilon * ((theta ^ 3) x.1 * theta x.2) +
        x.2 * (theta ^ 2) x.2 := by
  simp [typeDQuadraticMap]

/-- Higman's condition on `ε` for type `D`: the defining quadratic map has no
nonzero isotropic vector with both coordinates nonzero. -/
def IsTypeDEpsilon (theta : RingAut F) (epsilon : F) : Prop :=
  ∀ a b : F, a ≠ 0 → b ≠ 0 →
    a * theta a + epsilon * ((theta ^ 3) a * theta b) + b * (theta ^ 2) b ≠ 0

omit [Finite F] in
/-- Higman's condition on `ε` makes the type-`D` defining map anisotropic. -/
theorem typeDQuadraticMap_anisotropic (theta : RingAut F) (epsilon : F)
    (hε : IsTypeDEpsilon theta epsilon) :
    (typeDQuadraticMap theta epsilon).Anisotropic := by
  rintro ⟨a, b⟩ hq
  simp only [typeDQuadraticMap_apply] at hq
  by_cases ha : a = 0
  · subst a
    have hb : b = 0 := by simpa using hq
    subst b
    rfl
  by_cases hb : b = 0
  · subst b
    have ha0 : a = 0 := by simpa using hq
    exact (ha ha0).elim
  exact (hε a b ha hb hq).elim

/-- Higman's concrete group `D(n, θ, ε)` as the quadratic central extension of
the map in the type-`D` row of the p. 81 table. -/
abbrev TypeDModel (theta : RingAut F) (epsilon : F) :=
  QuadraticExtension (typeDQuadraticMap theta epsilon)
    (Module.finBasis (ZMod 2) (F × F))

namespace TypeDModel

/-- Squaring in `D(n, θ, ε)` is the type-`D` quadratic map. -/
theorem sq_eq_inl_quadraticMap (theta : RingAut F) (epsilon : F)
    (x : TypeDModel theta epsilon) :
    x ^ 2 =
      (QuadraticExtension.extension
        (typeDQuadraticMap theta epsilon)
        (Module.finBasis (ZMod 2) (F × F))).inl
          (Multiplicative.ofAdd
            (x.quotient.1 * theta x.quotient.1 +
              epsilon * ((theta ^ 3) x.quotient.1 * theta x.quotient.2) +
              x.quotient.2 * (theta ^ 2) x.quotient.2)) := by
  simpa only [typeDQuadraticMap_apply] using
    QuadraticExtension.sq_eq_inl_q
      (typeDQuadraticMap theta epsilon)
      (Module.finBasis (ZMod 2) (F × F)) x

end TypeDModel

end TypeModels

/-! ## Honest data carriers -/

/-- **Higman p. 81, type `C`.**  Honest data witnessing that `P` is a Suzuki
`2`-group of type `C`.

The field has order `2^n`; `θ` satisfies Higman's `2θ² = 1` (as automorphisms,
`frobeniusEquiv F 2 * θ² = 1`); `ε` satisfies the type-`C` nonvanishing
condition; and `equivModel` identifies `P` with the actual quadratic central
extension `C(n, ε)`. -/
structure TypeCData (P : Type uP) [Group P] where
  F : Type uF
  [fieldF : Field F]
  [finiteF : Finite F]
  [charTwoF : CharP F 2]
  parameter : ℕ
  parameter_pos : 0 < parameter
  card_field : Nat.card F = 2 ^ parameter
  theta : RingAut F
  theta_two_sq : frobeniusEquiv F 2 * theta ^ 2 = 1
  epsilon : Fˣ
  epsilon_anisotropic : IsTypeCEpsilon theta (epsilon : F)
  equivModel : P ≃* TypeCModel theta (epsilon : F)

/-- A group is of type `C` precisely when it carries the concrete data from the
type-`C` row of Higman's p. 81 table. -/
def IsTypeC (P : Type uP) [Group P] : Prop :=
  Nonempty (TypeCData.{uP, uF} P)

namespace TypeCData

/-- Build honest type-`C` data from an actual central extension whose square
coordinate is Higman's type-`C` map. -/
noncomputable def ofExtension
    {P : Type uP} [Group P]
    {F : Type uF} [Field F] [Finite F] [CharP F 2]
    (parameter : ℕ) (parameter_pos : 0 < parameter)
    (card_field : Nat.card F = 2 ^ parameter)
    (theta : RingAut F)
    (theta_two_sq : frobeniusEquiv F 2 * theta ^ 2 = 1)
    (epsilon : Fˣ)
    (epsilon_anisotropic : IsTypeCEpsilon theta (epsilon : F))
    (S : GroupExtension (Multiplicative F) P (Multiplicative (F × F)))
    (hcentral : S.inl.range ≤ Subgroup.center P)
    (hsq : ∀ x : P, x ^ 2 =
      S.inl (Multiplicative.ofAdd
        (typeCQuadraticMap theta (epsilon : F) (S.rightHom x).toAdd))) :
    TypeCData P := by
  letI : Algebra (ZMod 2) F := ZMod.algebra F 2
  let q := typeCQuadraticMap theta (epsilon : F)
  let basis := Module.finBasis (ZMod 2) (F × F)
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
      theta := theta
      theta_two_sq := theta_two_sq
      epsilon := epsilon
      epsilon_anisotropic := epsilon_anisotropic
      equivModel := extEquiv.toMulEquiv }

variable {P : Type uP} [Group P] (data : TypeCData P)

local instance : Field data.F := data.fieldF
local instance : Finite data.F := data.finiteF
local instance : CharP data.F 2 := data.charTwoF
local instance : Algebra (ZMod 2) data.F := ZMod.algebra data.F 2

/-- The field size attached to a type-`C` model. -/
theorem card_field_eq : Nat.card data.F = 2 ^ data.parameter :=
  data.card_field

/-- The source-level nonvanishing condition, exposed without the wrapper
predicate. -/
theorem quadraticMap_ne_zero (a b : data.F) (ha : a ≠ 0) (hb : b ≠ 0) :
    a * data.theta a +
        (data.epsilon : data.F) *
          ((frobeniusEquiv data.F 2)⁻¹ a *
            (frobeniusEquiv data.F 2 * data.theta) b) +
        b * b ≠ 0 :=
  data.epsilon_anisotropic a b ha hb

/-- The quadratic map of a concrete type-`C` model is anisotropic. -/
theorem quadraticMap_anisotropic :
    (typeCQuadraticMap data.theta (data.epsilon : data.F)).Anisotropic :=
  typeCQuadraticMap_anisotropic data.theta (data.epsilon : data.F)
    data.epsilon_anisotropic

/-- Squaring in any concrete type-`C` group is transported from the defining
quadratic extension. -/
theorem map_sq (x : P) :
    data.equivModel (x ^ 2) =
      (QuadraticExtension.extension
        (typeCQuadraticMap data.theta (data.epsilon : data.F))
        (Module.finBasis (ZMod 2) (data.F × data.F))).inl
          (Multiplicative.ofAdd
            ((data.equivModel x).quotient.1 *
                data.theta (data.equivModel x).quotient.1 +
              (data.epsilon : data.F) *
                ((frobeniusEquiv data.F 2)⁻¹ (data.equivModel x).quotient.1 *
                  (frobeniusEquiv data.F 2 * data.theta)
                    (data.equivModel x).quotient.2) +
              (data.equivModel x).quotient.2 *
                (data.equivModel x).quotient.2)) := by
  rw [map_pow]
  exact TypeCModel.sq_eq_inl_quadraticMap
    data.theta (data.epsilon : data.F) (data.equivModel x)

end TypeCData

/-- **Higman p. 81, type `D`.**  Honest data witnessing that `P` is a Suzuki
`2`-group of type `D`.

The field has order `2^n`; `θ` has order `5` (`θ⁵ = 1`, `θ ≠ 1`); `ε` satisfies
the type-`D` nonvanishing condition; and `equivModel` identifies `P` with the
actual quadratic central extension `D(n, θ, ε)`. -/
structure TypeDData (P : Type uP) [Group P] where
  F : Type uF
  [fieldF : Field F]
  [finiteF : Finite F]
  [charTwoF : CharP F 2]
  parameter : ℕ
  parameter_pos : 0 < parameter
  card_field : Nat.card F = 2 ^ parameter
  theta : RingAut F
  theta_pow_five : theta ^ 5 = 1
  theta_ne_one : theta ≠ 1
  epsilon : Fˣ
  epsilon_anisotropic : IsTypeDEpsilon theta (epsilon : F)
  equivModel : P ≃* TypeDModel theta (epsilon : F)

/-- A group is of type `D` precisely when it carries the concrete data from the
type-`D` row of Higman's p. 81 table. -/
def IsTypeD (P : Type uP) [Group P] : Prop :=
  Nonempty (TypeDData.{uP, uF} P)

namespace TypeDData

/-- Build honest type-`D` data from an actual central extension whose square
coordinate is Higman's type-`D` map. -/
noncomputable def ofExtension
    {P : Type uP} [Group P]
    {F : Type uF} [Field F] [Finite F] [CharP F 2]
    (parameter : ℕ) (parameter_pos : 0 < parameter)
    (card_field : Nat.card F = 2 ^ parameter)
    (theta : RingAut F)
    (theta_pow_five : theta ^ 5 = 1)
    (theta_ne_one : theta ≠ 1)
    (epsilon : Fˣ)
    (epsilon_anisotropic : IsTypeDEpsilon theta (epsilon : F))
    (S : GroupExtension (Multiplicative F) P (Multiplicative (F × F)))
    (hcentral : S.inl.range ≤ Subgroup.center P)
    (hsq : ∀ x : P, x ^ 2 =
      S.inl (Multiplicative.ofAdd
        (typeDQuadraticMap theta (epsilon : F) (S.rightHom x).toAdd))) :
    TypeDData P := by
  letI : Algebra (ZMod 2) F := ZMod.algebra F 2
  let q := typeDQuadraticMap theta (epsilon : F)
  let basis := Module.finBasis (ZMod 2) (F × F)
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
      theta := theta
      theta_pow_five := theta_pow_five
      theta_ne_one := theta_ne_one
      epsilon := epsilon
      epsilon_anisotropic := epsilon_anisotropic
      equivModel := extEquiv.toMulEquiv }

variable {P : Type uP} [Group P] (data : TypeDData P)

local instance : Field data.F := data.fieldF
local instance : Finite data.F := data.finiteF
local instance : CharP data.F 2 := data.charTwoF
local instance : Algebra (ZMod 2) data.F := ZMod.algebra data.F 2

/-- The field size attached to a type-`D` model. -/
theorem card_field_eq : Nat.card data.F = 2 ^ data.parameter :=
  data.card_field

/-- The source-level nonvanishing condition, exposed without the wrapper
predicate. -/
theorem quadraticMap_ne_zero (a b : data.F) (ha : a ≠ 0) (hb : b ≠ 0) :
    a * data.theta a +
        (data.epsilon : data.F) *
          ((data.theta ^ 3) a * data.theta b) +
        b * (data.theta ^ 2) b ≠ 0 :=
  data.epsilon_anisotropic a b ha hb

/-- The quadratic map of a concrete type-`D` model is anisotropic. -/
theorem quadraticMap_anisotropic :
    (typeDQuadraticMap data.theta (data.epsilon : data.F)).Anisotropic :=
  typeDQuadraticMap_anisotropic data.theta (data.epsilon : data.F)
    data.epsilon_anisotropic

/-- Squaring in any concrete type-`D` group is transported from the defining
quadratic extension. -/
theorem map_sq (x : P) :
    data.equivModel (x ^ 2) =
      (QuadraticExtension.extension
        (typeDQuadraticMap data.theta (data.epsilon : data.F))
        (Module.finBasis (ZMod 2) (data.F × data.F))).inl
          (Multiplicative.ofAdd
            ((data.equivModel x).quotient.1 *
                data.theta (data.equivModel x).quotient.1 +
              (data.epsilon : data.F) *
                ((data.theta ^ 3) (data.equivModel x).quotient.1 *
                  data.theta (data.equivModel x).quotient.2) +
              (data.equivModel x).quotient.2 *
                (data.theta ^ 2) (data.equivModel x).quotient.2)) := by
  rw [map_pow]
  exact TypeDModel.sq_eq_inl_quadraticMap
    data.theta (data.epsilon : data.F) (data.equivModel x)

end TypeDData

end

end OddOrder.Higman.Suzuki2Groups
