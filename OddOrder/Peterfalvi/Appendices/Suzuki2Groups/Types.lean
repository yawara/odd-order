/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Algebra.Algebra.ZMod
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Prod
import OddOrder.Peterfalvi.Appendices.Suzuki2Groups.QuadraticExtensions

/-!
# Peterfalvi Appendix III: Suzuki 2-group types A and B

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Appendix III, Definitions 2--3, p. 140.

This file gives the concrete quadratic-map models occurring in Definitions
2--3.  Definition 2 uses `a |-> a * phi(a)`.  For Definition 3, given a finite
field `F` of characteristic two, a field automorphism `phi`, and
`epsilon : F^x`, the map

`(a, b) |-> a * phi(a) + epsilon * a * phi(b) + b * phi(b)`

is constructed as an actual `QuadraticMap (ZMod 2) (F x F) F`.  The resulting
quadratic extensions are Peterfalvi's groups `A(n, phi)` and
`B(n, phi, epsilon)`.  Thus `TypeAData P` and `TypeBData P` contain genuine
group equivalences rather than proposition-valued classification labels.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki2Groups

noncomputable section

universe uP uF

section TypeModels

variable {F : Type uF} [Field F] [CharP F 2]

local instance : Algebra (ZMod 2) F := ZMod.algebra F 2

/-- A field automorphism in characteristic two, regarded as an `F_2`-linear
map.  Additivity is enough: every additive homomorphism between `ZMod 2`
modules is automatically `ZMod 2`-linear. -/
def ringAutToZModLinear (phi : RingAut F) : F →ₗ[ZMod 2] F :=
  phi.toAddEquiv.toAddMonoidHom.toZModLinearMap 2

@[simp]
theorem ringAutToZModLinear_apply (phi : RingAut F) (a : F) :
    ringAutToZModLinear phi a = phi a :=
  rfl

/-- **Peterfalvi Appendix III, Definition 2.**  The quadratic map defining
`A(n, phi)`. -/
def typeAQuadraticMap (phi : RingAut F) : QuadraticMap (ZMod 2) F F :=
  QuadraticMap.linMulLin LinearMap.id (ringAutToZModLinear phi)

@[simp]
theorem typeAQuadraticMap_apply (phi : RingAut F) (a : F) :
    typeAQuadraticMap phi a = a * phi a :=
  rfl

/-- Peterfalvi's concrete group `A(n, phi)`, obtained from the quadratic map
in Definition 2 by Appendix III, Lemma 1(b). -/
abbrev TypeAModel [Finite F] (phi : RingAut F) :=
  QuadraticExtension (typeAQuadraticMap phi)
    (Module.finBasis (ZMod 2) F)

namespace TypeAModel

variable [Finite F] (phi : RingAut F)

/-- Squaring in `A(n, phi)` is `a |-> a * phi(a)`. -/
theorem sq_eq_inl_quadraticMap (x : TypeAModel phi) :
    x ^ 2 =
      (QuadraticExtension.extension
        (typeAQuadraticMap phi)
        (Module.finBasis (ZMod 2) F)).inl
          (Multiplicative.ofAdd (x.quotient * phi x.quotient)) := by
  simpa only [typeAQuadraticMap_apply] using
    QuadraticExtension.sq_eq_inl_q
      (typeAQuadraticMap phi) (Module.finBasis (ZMod 2) F) x

end TypeAModel

/-- **Peterfalvi Appendix III, Definition 3.**  The quadratic map defining
`B(n, phi, epsilon)`.

The three summands are built with `QuadraticMap.linMulLin`; in particular, this
is an actual quadratic map over `F_2`, not a separately posited quadratic-law
field. -/
def typeBQuadraticMap (phi : RingAut F) (epsilon : F) :
    QuadraticMap (ZMod 2) (F × F) F :=
  QuadraticMap.linMulLin
      (LinearMap.fst (ZMod 2) F F)
      ((ringAutToZModLinear phi).comp (LinearMap.fst (ZMod 2) F F)) +
    epsilon • QuadraticMap.linMulLin
      (LinearMap.fst (ZMod 2) F F)
      ((ringAutToZModLinear phi).comp (LinearMap.snd (ZMod 2) F F)) +
    QuadraticMap.linMulLin
      (LinearMap.snd (ZMod 2) F F)
      ((ringAutToZModLinear phi).comp (LinearMap.snd (ZMod 2) F F))

@[simp]
theorem typeBQuadraticMap_apply (phi : RingAut F) (epsilon : F) (x : F × F) :
    typeBQuadraticMap phi epsilon x =
      x.1 * phi x.1 + epsilon * (x.1 * phi x.2) + x.2 * phi x.2 :=
  by simp [typeBQuadraticMap]

/-- The condition on `epsilon` in Appendix III, Definition 3.  Peterfalvi
requires the displayed value to be nonzero when both coordinates are nonzero.
-/
def IsTypeBEpsilon (phi : RingAut F) (epsilon : F) : Prop :=
  ∀ a b : F, a ≠ 0 → b ≠ 0 →
    a * phi a + epsilon * (a * phi b) + b * phi b ≠ 0

/-- Peterfalvi's condition on `epsilon` makes the full defining quadratic map
anisotropic.  The cases in which one coordinate is zero follow from the field
property; the case in which both are nonzero is exactly Definition 3. -/
theorem typeBQuadraticMap_anisotropic (phi : RingAut F) (epsilon : F)
    (hε : IsTypeBEpsilon phi epsilon) :
    (typeBQuadraticMap phi epsilon).Anisotropic := by
  rintro ⟨a, b⟩ hq
  simp only [typeBQuadraticMap_apply] at hq
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

/-- Peterfalvi's concrete group `B(n, phi, epsilon)`, obtained from the
quadratic map in Definition 3 by Appendix III, Lemma 1(b).

`QuadraticExtension` uses an ordered basis to choose a bilinear lift.  The
canonical finite basis is a construction choice for that lift and is not
additional classification data. -/
abbrev TypeBModel [Finite F] (phi : RingAut F) (epsilon : F) :=
  QuadraticExtension (typeBQuadraticMap phi epsilon)
    (Module.finBasis (ZMod 2) (F × F))

namespace TypeBModel

variable [Finite F] (phi : RingAut F) (epsilon : F)

/-- Squaring in `B(n, phi, epsilon)` is the quadratic map from Definition 3. -/
theorem sq_eq_inl_quadraticMap (x : TypeBModel phi epsilon) :
    x ^ 2 =
      (QuadraticExtension.extension
        (typeBQuadraticMap phi epsilon)
        (Module.finBasis (ZMod 2) (F × F))).inl
          (Multiplicative.ofAdd
            (x.quotient.1 * phi x.quotient.1 +
              epsilon * (x.quotient.1 * phi x.quotient.2) +
              x.quotient.2 * phi x.quotient.2)) := by
  simpa only [typeBQuadraticMap_apply] using
    QuadraticExtension.sq_eq_inl_q
      (typeBQuadraticMap phi epsilon)
      (Module.finBasis (ZMod 2) (F × F)) x

end TypeBModel

end TypeModels

/-- **Peterfalvi Appendix III, Definition 2.**  Honest data witnessing that
`P` is a Suzuki `2`-group of type A.

The field has order `2^n`; `phi` is nontrivial and has odd order; and
`equivModel` identifies `P` with the actual quadratic central extension
`A(n, phi)`. -/
structure TypeAData (P : Type uP) [Group P] where
  F : Type uF
  [fieldF : Field F]
  [finiteF : Finite F]
  [charTwoF : CharP F 2]
  parameter : ℕ
  parameter_pos : 0 < parameter
  card_field : Nat.card F = 2 ^ parameter
  phi : RingAut F
  phi_ne_one : phi ≠ 1
  phi_orderOf_odd : Odd (orderOf phi)
  equivModel : P ≃* TypeAModel phi

/-- A group is of type A precisely when it carries the concrete data from
Appendix III, Definition 2. -/
def IsTypeA (P : Type uP) [Group P] : Prop :=
  Nonempty (TypeAData.{uP, uF} P)

namespace TypeAData

variable {P : Type uP} [Group P] (data : TypeAData P)

local instance : Field data.F := data.fieldF
local instance : Finite data.F := data.finiteF
local instance : CharP data.F 2 := data.charTwoF
local instance : Algebra (ZMod 2) data.F := ZMod.algebra data.F 2

/-- The field size attached to a type-A model. -/
theorem card_field_eq : Nat.card data.F = 2 ^ data.parameter :=
  data.card_field

/-- Squaring in any concrete type-A group is transported from the defining
quadratic extension. -/
theorem map_sq (x : P) :
    data.equivModel (x ^ 2) =
      (QuadraticExtension.extension
        (typeAQuadraticMap data.phi)
        (Module.finBasis (ZMod 2) data.F)).inl
          (Multiplicative.ofAdd
            ((data.equivModel x).quotient *
              data.phi (data.equivModel x).quotient)) := by
  rw [map_pow]
  exact TypeAModel.sq_eq_inl_quadraticMap data.phi (data.equivModel x)

end TypeAData

/-- **Peterfalvi Appendix III, Definition 3.**  Honest data witnessing that
`P` is a Suzuki `2`-group of type B.

The field has the stated order `2^n`; `phi` has odd order; `epsilon` satisfies
Peterfalvi's nonvanishing condition; and `equivModel` identifies `P` with the
actual quadratic central extension `B(n, phi, epsilon)`. -/
structure TypeBData (P : Type uP) [Group P] where
  F : Type uF
  [fieldF : Field F]
  [finiteF : Finite F]
  [charTwoF : CharP F 2]
  parameter : ℕ
  parameter_pos : 0 < parameter
  card_field : Nat.card F = 2 ^ parameter
  phi : RingAut F
  phi_orderOf_odd : Odd (orderOf phi)
  epsilon : Fˣ
  epsilon_anisotropic : IsTypeBEpsilon phi (epsilon : F)
  equivModel : P ≃* TypeBModel phi (epsilon : F)

/-- A group is of type B precisely when it carries the concrete data from
Appendix III, Definition 3. -/
def IsTypeB (P : Type uP) [Group P] : Prop :=
  Nonempty (TypeBData.{uP, uF} P)

namespace TypeBData

variable {P : Type uP} [Group P] (data : TypeBData P)

local instance : Field data.F := data.fieldF
local instance : Finite data.F := data.finiteF
local instance : CharP data.F 2 := data.charTwoF
local instance : Algebra (ZMod 2) data.F := ZMod.algebra data.F 2

/-- The field size attached to a type-B model. -/
theorem card_field_eq : Nat.card data.F = 2 ^ data.parameter :=
  data.card_field

/-- The source-level nonvanishing condition, exposed without the wrapper
predicate. -/
theorem quadraticMap_ne_zero (a b : data.F) (ha : a ≠ 0) (hb : b ≠ 0) :
    a * data.phi a + (data.epsilon : data.F) * (a * data.phi b) +
        b * data.phi b ≠ 0 :=
  data.epsilon_anisotropic a b ha hb

/-- The quadratic map of a concrete type-B model is anisotropic. -/
theorem quadraticMap_anisotropic :
    (typeBQuadraticMap data.phi (data.epsilon : data.F)).Anisotropic :=
  typeBQuadraticMap_anisotropic data.phi (data.epsilon : data.F)
    data.epsilon_anisotropic

/-- Squaring in any concrete type-B group is transported from the defining
quadratic extension. -/
theorem map_sq (x : P) :
    data.equivModel (x ^ 2) =
      (QuadraticExtension.extension
        (typeBQuadraticMap data.phi (data.epsilon : data.F))
        (Module.finBasis (ZMod 2) (data.F × data.F))).inl
          (Multiplicative.ofAdd
            ((data.equivModel x).quotient.1 *
                data.phi (data.equivModel x).quotient.1 +
              (data.epsilon : data.F) *
                ((data.equivModel x).quotient.1 *
                  data.phi (data.equivModel x).quotient.2) +
              (data.equivModel x).quotient.2 *
                data.phi (data.equivModel x).quotient.2)) := by
  rw [map_pow]
  exact TypeBModel.sq_eq_inl_quadraticMap
    data.phi (data.epsilon : data.F) (data.equivModel x)

end TypeBData

end

end OddOrder.Peterfalvi.Appendices.Suzuki2Groups
