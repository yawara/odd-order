/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.Classification

/-!
# Exponent four for Higman's Suzuki 2-groups

G. Higman, “Suzuki 2-groups,” *Illinois Journal of Mathematics* 7 (1963),
Theorem 1(a), pp. 79–82.

Higman's four classified families are concrete quadratic central extensions
over `ZMod 2`.  In every such extension, the square of an element belongs to
the elementary abelian kernel, so its fourth power is one.  Transporting this
calculation through the honest type-`A`/`B`/`C`/`D` model equivalences and then
applying the classification theorem proves the exponent-four clause for every
Suzuki `2`-group.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

open OddOrder.GroupTheory.Suzuki2Group
open OddOrder.Peterfalvi.Appendices.Suzuki2Groups
open Module

noncomputable section

universe uP uF uV uW uI

/-- Every quadratic extension of `ZMod 2`-modules has exponent dividing four:
squaring lands in its elementary abelian kernel. -/
private theorem quadraticExtension_pow_four_eq_one
    {V : Type uV} {W : Type uW} {ι : Type uI}
    [LinearOrder ι] [AddCommGroup V] [AddCommGroup W]
    [Module (ZMod 2) V] [Module (ZMod 2) W]
    (q : QuadraticMap (ZMod 2) V W) (basis : Basis ι (ZMod 2) V)
    (x : QuadraticExtension q basis) :
    x ^ 4 = 1 := by
  have hker :
      (Multiplicative.ofAdd (q x.quotient)) ^ 2 = 1 := by
    apply Multiplicative.toAdd.injective
    simp only [toAdd_pow, toAdd_ofAdd, toAdd_one]
    calc
      2 • q x.quotient = (2 : ZMod 2) • q x.quotient :=
        (Nat.cast_smul_eq_nsmul (ZMod 2) 2 _).symm
      _ = 0 := by
        rw [show (2 : ZMod 2) = 0 by decide, zero_smul]
  calc
    x ^ 4 = (x ^ 2) ^ 2 := by
      rw [show (4 : ℕ) = 2 * 2 by decide, pow_mul]
    _ = ((QuadraticExtension.extension q basis).inl
          (Multiplicative.ofAdd (q x.quotient))) ^ 2 := by
      exact congrArg (fun y => y ^ 2)
        (QuadraticExtension.sq_eq_inl_q q basis x)
    _ = (QuadraticExtension.extension q basis).inl
          ((Multiplicative.ofAdd (q x.quotient)) ^ 2) := by
      rw [map_pow]
    _ = 1 := by rw [hker, map_one]

/-- Every group of Higman's type `A` has exponent dividing four. -/
theorem pow_four_eq_one_of_isTypeA
    {P : Type uP} [Group P] (hP : IsTypeA.{uP, uF} P) (x : P) :
    x ^ 4 = 1 := by
  obtain ⟨data⟩ := hP
  letI := data.fieldF
  letI := data.finiteF
  letI := data.charTwoF
  letI : Algebra (ZMod 2) data.F := ZMod.algebra data.F 2
  apply data.equivModel.injective
  rw [map_pow, map_one]
  exact quadraticExtension_pow_four_eq_one
    (typeAQuadraticMap data.phi) (Module.finBasis (ZMod 2) data.F)
      (data.equivModel x)

/-- Every group of Higman's type `B` has exponent dividing four. -/
theorem pow_four_eq_one_of_isTypeB
    {P : Type uP} [Group P] (hP : IsTypeB.{uP, uF} P) (x : P) :
    x ^ 4 = 1 := by
  obtain ⟨data⟩ := hP
  letI := data.fieldF
  letI := data.finiteF
  letI := data.charTwoF
  letI : Algebra (ZMod 2) data.F := ZMod.algebra data.F 2
  apply data.equivModel.injective
  rw [map_pow, map_one]
  exact quadraticExtension_pow_four_eq_one
    (typeBQuadraticMap data.phi (data.epsilon : data.F))
      (Module.finBasis (ZMod 2) (data.F × data.F)) (data.equivModel x)

/-- Every group of Higman's type `C` has exponent dividing four. -/
theorem pow_four_eq_one_of_isTypeC
    {P : Type uP} [Group P] (hP : IsTypeC.{uP, uF} P) (x : P) :
    x ^ 4 = 1 := by
  obtain ⟨data⟩ := hP
  letI := data.fieldF
  letI := data.finiteF
  letI := data.charTwoF
  letI : Algebra (ZMod 2) data.F := ZMod.algebra data.F 2
  apply data.equivModel.injective
  rw [map_pow, map_one]
  exact quadraticExtension_pow_four_eq_one
    (typeCQuadraticMap data.theta (data.epsilon : data.F))
      (Module.finBasis (ZMod 2) (data.F × data.F)) (data.equivModel x)

/-- Every group of Higman's type `D` has exponent dividing four. -/
theorem pow_four_eq_one_of_isTypeD
    {P : Type uP} [Group P] (hP : IsTypeD.{uP, uF} P) (x : P) :
    x ^ 4 = 1 := by
  obtain ⟨data⟩ := hP
  letI := data.fieldF
  letI := data.finiteF
  letI := data.charTwoF
  letI : Algebra (ZMod 2) data.F := ZMod.algebra data.F 2
  apply data.equivModel.injective
  rw [map_pow, map_one]
  exact quadraticExtension_pow_four_eq_one
    (typeDQuadraticMap data.theta (data.epsilon : data.F))
      (Module.finBasis (ZMod 2) (data.F × data.F)) (data.equivModel x)

/-- The exponent-four conclusion for the disjunction produced by Higman's
classification theorem. -/
theorem pow_four_eq_one_of_higmanType
    {P : Type uP} [Group P]
    (hP : IsTypeA.{uP, 0} P ∨ IsTypeB.{uP, 0} P ∨
      IsTypeC.{uP, 0} P ∨ IsTypeD.{uP, 0} P)
    (x : P) :
    x ^ 4 = 1 := by
  rcases hP with hA | hB | hC | hD
  · obtain ⟨data⟩ := hA
    exact pow_four_eq_one_of_isTypeA ⟨data⟩ x
  · obtain ⟨data⟩ := hB
    exact pow_four_eq_one_of_isTypeB ⟨data⟩ x
  · obtain ⟨data⟩ := hC
    exact pow_four_eq_one_of_isTypeC ⟨data⟩ x
  · obtain ⟨data⟩ := hD
    exact pow_four_eq_one_of_isTypeD ⟨data⟩ x

/-- **Higman, Suzuki 2-groups, Theorem 1(a).** Every Suzuki `2`-group has
exponent dividing four. -/
theorem pow_four_eq_one_of_isSuzuki2Group
    {P : Type uP} [Group P] [Finite P]
    (hP : IsSuzuki2Group P) (x : P) :
    x ^ 4 = 1 :=
  pow_four_eq_one_of_higmanType
    (higmanClassification_of_isSuzuki2Group hP) x

end

end OddOrder.Higman.Suzuki2Groups
