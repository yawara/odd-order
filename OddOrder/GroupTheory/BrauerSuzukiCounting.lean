/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.BrauerSuzukiInvolutions
import OddOrder.GroupTheory.BrauerSuzukiCharacter
import OddOrder.GroupTheory.RepresentationTheory.ClassSumCoefficientFormula

/-!
# Brauer–Suzuki: counting involution pairs (Gorenstein Ch. 12, towards Lemma 1.8)

**Gorenstein, *Finite Groups*, Ch. 12, Lemma 1.8** derives the character relation
`1 + χ₁(u)²/χ₁(1) − χ(u)²/χ(1) = 0` from the class-sum structure-constant formula `(9.4.2)`
applied to `β(y) = #{(u, v) : u, v involutions, uv = y}`.

This file assembles the pieces on the counting side.  Working with the *class-summed*
coefficient `classSumCoeff K K Cs` (over the whole target class `Cs`) rather than the
per-element `β(y)` lets us reuse `classSumCoeff_mul_centralizer_card_eq_sum_irreducibleCharacter`
directly.  The involutions of `G` form the single conjugacy class `K = mk z`
(`isConj_z_iff_orderOf_eq_two`), and:

* `classSumCoeff K K Cs = 0` whenever `Cs` has even order, because the product of two
  involutions has odd order (`odd_orderOf_mul_of_involution`).
-/

open OddOrder.RepresentationTheory

namespace OddOrder.GroupTheory

/-- `IsConj` preserves order. -/
theorem orderOf_eq_of_isConj {G : Type*} [Group G] {a b : G} (h : IsConj a b) :
    orderOf a = orderOf b := by
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  rw [← hc]
  exact SemiconjBy.orderOf_eq c (show SemiconjBy c a (c * a * c⁻¹) by
    change c * a = c * a * c⁻¹ * c; group)

namespace QuaternionSylowSetup

variable {G : Type*} [Group G] [Finite G] (Q : QuaternionSylowSetup G)

/-- The conjugacy class `K` of involutions of `G` (all involutions are conjugate to `z`). -/
def involutionClass : ConjClasses G := ConjClasses.mk Q.z

include Q

/-- `u` lies in the involution class iff `u` is an involution. -/
theorem mk_eq_involutionClass_iff {u : G} :
    ConjClasses.mk u = Q.involutionClass ↔ orderOf u = 2 := by
  rw [involutionClass, ConjClasses.mk_eq_mk_iff_isConj, Q.isConj_z_iff_orderOf_eq_two]

/-- **`classSumCoeff K K Cs = 0` for a class `Cs` of even order** (towards Gorenstein Lemma 1.8):
no ordered pair of involutions multiplies to an element of `Cs`, since the product of two
involutions has odd order (`odd_orderOf_mul_of_involution`) while every element of `Cs` has the
same even order. -/
theorem classSumCoeff_involutionClass_eq_zero_of_even
    [Fintype G] [DecidableEq (ConjClasses G)] {Cs : ConjClasses G}
    (hCs : Even (orderOf Cs.out)) :
    classSumCoeff Q.involutionClass Q.involutionClass Cs = 0 := by
  classical
  rw [classSumCoeff, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro ⟨u, v⟩ -
  rintro ⟨hu, hv, huv⟩
  have hu2 : orderOf u = 2 := Q.mk_eq_involutionClass_iff.mp hu
  have hv2 : orderOf v = 2 := Q.mk_eq_involutionClass_iff.mp hv
  have hodd : Odd (orderOf (u * v)) := Q.odd_orderOf_mul_of_involution hu2 hv2
  have hconj : IsConj (u * v) Cs.out := by
    rw [← ConjClasses.mk_eq_mk_iff_isConj, huv, conjClass_mk_out]
  rw [orderOf_eq_of_isConj hconj] at hodd
  exact (Nat.not_even_iff_odd.mpr hodd) hCs

/-- **`∑_Cs classSumCoeff K K Cs · θ*(Cs.out) = 0`** (Gorenstein Lemma 1.8, `β·θ* = 0` summed
by class).  Each term vanishes: if `Cs.out` has even order then `classSumCoeff K K Cs = 0`
(`classSumCoeff_involutionClass_eq_zero_of_even`); if it has odd order then `θ*(Cs.out) = 0`
(`thetaStar_apply_eq_zero_of_odd`, Lemma 1.6). -/
theorem sum_classSumCoeff_thetaStar_eq_zero
    [Fintype G] [Fintype ↥Q.N] [Fintype (ConjClasses G)] [DecidableEq (ConjClasses G)]
    [Invertible (Nat.card ↥Q.N : ℂ)] [Invertible (Nat.card ↥(Q.C.subgroupOf Q.N) : ℂ)] :
    ∑ Cs : ConjClasses G,
      (classSumCoeff Q.involutionClass Q.involutionClass Cs : ℂ) * Q.thetaStar Cs.out = 0 := by
  apply Finset.sum_eq_zero
  intro Cs _
  rcases Nat.even_or_odd (orderOf Cs.out) with heven | hodd
  · rw [Q.classSumCoeff_involutionClass_eq_zero_of_even heven, Nat.cast_zero, zero_mul]
  · rw [Q.thetaStar_apply_eq_zero_of_odd hodd, mul_zero]

/-- **The `(9.4.2)`-weighted class sum equals the inner product `⟨θ*, χ⟩`** (Gorenstein
Lemma 1.8, the bridge from the class-sum formula to character multiplicities).  Summing
`θ*(Cs.out)·χ(Cs.out⁻¹)` weighted by `1/|C_G(Cs.out)|` over conjugacy classes reproduces the
normalized inner product `⟨θ*, χ⟩ = ⅟|G| · ∑_g θ*(g)·conj(χ(g))`, using the orbit-stabilizer
identity `|Cs|·|C_G(Cs.out)| = |G|` and `χ(g⁻¹) = conj(χ(g))`. -/
theorem sum_thetaStar_char_div_centralizer_eq_inner
    [Fintype G] [Fintype ↥Q.N] [Fintype (ConjClasses G)]
    [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card ↥Q.N : ℂ)]
    [Invertible (Nat.card ↥(Q.C.subgroupOf Q.N) : ℂ)] (χ : IrreducibleCharacter G) :
    ∑ Cs : ConjClasses G, Q.thetaStar Cs.out * (χ : ClassFunction G ℂ) Cs.out⁻¹
        / (Nat.card (Subgroup.centralizer ({Cs.out} : Set G)) : ℂ)
      = ClassFunction.inner Q.thetaStar (χ : ClassFunction G ℂ) := by
  rw [ClassFunction.inner_eq_inv_card_mul_innerSum,
    classFunction_innerSum_eq_sum_conjClasses, Finset.mul_sum]
  refine Finset.sum_congr rfl fun Cs _ => ?_
  -- reconcile the representative `conjugacyClassRepresentative Cs` with `Cs.out`
  have hrepconj : IsConj (conjugacyClassRepresentative Cs) Cs.out := by
    rw [← ConjClasses.mk_eq_mk_iff_isConj, conjugacyClassRepresentative_mk_eq, conjClass_mk_out]
  have hθ : Q.thetaStar (conjugacyClassRepresentative Cs) = Q.thetaStar Cs.out :=
    Q.thetaStar.of_isConj hrepconj
  have hχ : (χ : ClassFunction G ℂ) (conjugacyClassRepresentative Cs)
      = (χ : ClassFunction G ℂ) Cs.out :=
    (χ : ClassFunction G ℂ).of_isConj hrepconj
  rw [hθ, hχ, irreducibleCharacter_apply_inv]
  -- orbit-stabilizer: `|Cs|·|C_G(Cs.out)| = |G|`
  have hcent : (conjugacyClassSize Cs : ℂ)
      * (Nat.card (Subgroup.centralizer ({Cs.out} : Set G)) : ℂ) = (Nat.card G : ℂ) := by
    have h := conjugacyClassSize_mk_mul_card_centralizer_cast (G := G) Cs.out
    rwa [conjClass_mk_out] at h
  have hgne : (Nat.card G : ℂ) ≠ 0 := Invertible.ne_zero _
  have hcentne : (Nat.card (Subgroup.centralizer ({Cs.out} : Set G)) : ℂ) ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hcent; exact hgne hcent.symm
  -- `1/|C_G(Cs.out)| = |Cs| · 1/|G|`
  have hc_inv : (Nat.card (Subgroup.centralizer ({Cs.out} : Set G)) : ℂ)⁻¹
      = (conjugacyClassSize Cs : ℂ) * (Nat.card G : ℂ)⁻¹ := by
    field_simp
    linear_combination -hcent
  rw [invOf_eq_inv, div_eq_mul_inv, hc_inv]; ring

/-- **`∑_χ (|K|·χ(u))²/χ(1) · ⟨θ*, χ⟩ = 0`** (Gorenstein Lemma 1.8, the character-sum form).
Substituting the class-sum formula `(9.4.2)` into `sum_classSumCoeff_thetaStar_eq_zero` and
recognizing the resulting weighted class sum as `⟨θ*, χ⟩`
(`sum_thetaStar_char_div_centralizer_eq_inner`) turns the vanishing class sum into a vanishing
sum over irreducible characters. -/
theorem sum_degWeight_inner_eq_zero
    [Fintype G] [Fintype ↥Q.N]
    [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card ↥Q.N : ℂ)]
    [Invertible (Nat.card ↥(Q.C.subgroupOf Q.N) : ℂ)] :
    ∑ χ : IrreducibleCharacter G,
        ((Nat.card { x : G // ConjClasses.mk x = Q.involutionClass } : ℂ)
              * (χ : ClassFunction G ℂ) Q.involutionClass.out
            * ((Nat.card { x : G // ConjClasses.mk x = Q.involutionClass } : ℂ)
              * (χ : ClassFunction G ℂ) Q.involutionClass.out)
          / (χ : ClassFunction G ℂ) 1)
          * ClassFunction.inner Q.thetaStar (χ : ClassFunction G ℂ) = 0 := by
  classical
  haveI : Fintype (ConjClasses G) := Fintype.ofFinite _
  rw [← Q.sum_classSumCoeff_thetaStar_eq_zero]
  -- rewrite `⟨θ*, χ⟩` as the weighted class sum, then swap the order of summation
  rw [Finset.sum_congr rfl fun χ _ => by
    rw [← Q.sum_thetaStar_char_div_centralizer_eq_inner χ, Finset.mul_sum], Finset.sum_comm]
  refine Finset.sum_congr rfl fun Cs _ => ?_
  -- per class `Cs`: the inner `∑_χ` reassembles the `(9.4.2)` right-hand side
  have h942 := classSumCoeff_mul_centralizer_card_eq_sum_irreducibleCharacter
    (G := G) Q.involutionClass Q.involutionClass Cs
  have hgne : (Nat.card G : ℂ) ≠ 0 := Invertible.ne_zero _
  have hcent : (conjugacyClassSize Cs : ℂ)
      * (Nat.card (Subgroup.centralizer ({Cs.out} : Set G)) : ℂ) = (Nat.card G : ℂ) := by
    have h := conjugacyClassSize_mk_mul_card_centralizer_cast (G := G) Cs.out
    rwa [conjClass_mk_out] at h
  have hcentne : (Nat.card (Subgroup.centralizer ({Cs.out} : Set G)) : ℂ) ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hcent; exact hgne hcent.symm
  -- factor `θ*(Cs.out)/|C_G|` out of the `∑_χ` (abstracting the `χ`-dependent factors as
  -- `a, b` to avoid coercion friction), then use `(9.4.2)`
  have reorder : ∀ a b : ℂ, a * (Q.thetaStar Cs.out * b
        / (Nat.card (Subgroup.centralizer ({Cs.out} : Set G)) : ℂ))
      = Q.thetaStar Cs.out / (Nat.card (Subgroup.centralizer ({Cs.out} : Set G)) : ℂ) * (a * b) :=
    fun a b => by ring
  simp_rw [reorder]
  rw [← Finset.mul_sum, ← h942]
  field_simp

end QuaternionSylowSetup

end OddOrder.GroupTheory
