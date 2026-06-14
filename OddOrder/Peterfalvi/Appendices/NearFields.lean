/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki

/-!
# Peterfalvi Appendix C: On Near-Fields

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Appendix C, pp. 137--138.

The appendix uses finite near-fields to describe the 2-rank one case of the
Suzuki theorem and records the special Zassenhaus classification needed there.
-/

namespace OddOrder.Peterfalvi.Appendices.NearFields
-- scaffold opaque-Prop convention: see notes/meta/scaffold_opaque_prop_convention.md

/-- A **(right) near-field** (Peterfalvi, Appendix C, p. 137): a set `F` with `+` and `·` such that
`(F, +)` is a commutative group, `(F, ·)` is a group with zero — i.e. `(F ∖ {0}, ·)` is a group —
and the **right** distributive law `(a + b) c = a c + b c` holds.  (Left distributivity and
`·`-commutativity may fail; a field is the special case where both also hold.)

Modeled as `AddCommGroup F` + `GroupWithZero F` + right distributivity, so the full multiplicative
group-with-zero API (`mul_inv_cancel₀`, `zero_mul`, `mul_zero`, `zero_ne_one`, …) is inherited. -/
class NearField (F : Type*) extends AddCommGroup F, GroupWithZero F where
  /-- The right distributive law `(a + b) * c = a * c + b * c`. -/
  protected right_distrib : ∀ a b c : F, (a + b) * c = a * c + b * c

/-- The right distributive law in a near-field. -/
theorem NearField.add_mul {F : Type*} [NearField F] (a b c : F) :
    (a + b) * c = a * c + b * c := NearField.right_distrib a b c

section NearFieldBasics

variable {F : Type*} [NearField F]

/-- Right multiplication by a nonzero element is an additive automorphism of a near-field: it is
additive by the right distributive law, and bijective because `a` is invertible. -/
def rightMul (a : F) (ha : a ≠ 0) : F ≃+ F where
  toFun x := x * a
  invFun x := x * a⁻¹
  left_inv x := by show (x * a) * a⁻¹ = x; rw [mul_assoc, mul_inv_cancel₀ ha, mul_one]
  right_inv x := by show (x * a⁻¹) * a = x; rw [mul_assoc, inv_mul_cancel₀ ha, mul_one]
  map_add' x y := NearField.add_mul x y a

@[simp] theorem rightMul_apply (a : F) (ha : a ≠ 0) (x : F) : rightMul a ha x = x * a := rfl

/-- All nonzero elements of a near-field have the same additive order: `F^*` acts transitively on
`F^#` by right multiplication (`rightMul`), an additive automorphism. -/
theorem addOrderOf_eq_of_ne_zero (x y : F) (hx : x ≠ 0) (hy : y ≠ 0) :
    addOrderOf x = addOrderOf y := by
  have hne : x⁻¹ * y ≠ 0 := mul_ne_zero (inv_ne_zero hx) hy
  have hxy : y = (rightMul (x⁻¹ * y) hne) x := by
    show y = x * (x⁻¹ * y); rw [← mul_assoc, mul_inv_cancel₀ hx, one_mul]
  rw [hxy]
  exact (addOrderOf_injective (rightMul (x⁻¹ * y) hne).toAddMonoidHom
    (rightMul (x⁻¹ * y) hne).injective x).symm

/-- **The characteristic of a finite near-field is a prime** (Peterfalvi, Appendix C, p. 137: "`F`
is an elementary abelian `f`-group for some prime `f`"): there is a prime `f` with `f • x = 0` for
all `x ∈ F`.  Since all nonzero elements share one additive order (`addOrderOf_eq_of_ne_zero`),
that order is forced to be prime by the divisor argument; this makes `(F, +)` elementary abelian. -/
theorem exists_prime_char [Finite F] [Nontrivial F] :
    ∃ f : ℕ, f.Prime ∧ ∀ x : F, f • x = 0 := by
  obtain ⟨x₀, hx₀⟩ := exists_ne (0 : F)
  set f := addOrderOf x₀ with hf
  have hf0 : f ≠ 0 := (addOrderOf_pos x₀).ne'
  have hf1 : f ≠ 1 := fun h => hx₀ (AddMonoid.addOrderOf_eq_one_iff.mp h)
  obtain ⟨g, hg_prime, hg_dvd⟩ := Nat.exists_prime_and_dvd hf1
  have hdvd2 : f / g ∣ f := Nat.div_dvd_of_dvd hg_dvd
  have hord : addOrderOf ((f / g) • x₀) = g := by
    rw [addOrderOf_nsmul, ← hf, Nat.gcd_eq_right hdvd2, Nat.div_div_self hg_dvd hf0]
  have hgf : g = f := by
    by_contra hne
    have hy0 : (f / g) • x₀ ≠ 0 := by
      intro h
      have h1 : addOrderOf ((f / g) • x₀) = 1 := AddMonoid.addOrderOf_eq_one_iff.mpr h
      rw [hord] at h1; exact hg_prime.ne_one h1
    have hconst := addOrderOf_eq_of_ne_zero ((f / g) • x₀) x₀ hy0 hx₀
    rw [hord, ← hf] at hconst
    exact hne hconst
  refine ⟨f, hgf ▸ hg_prime, fun x => ?_⟩
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · have hax : addOrderOf x = f := addOrderOf_eq_of_ne_zero x x₀ hx hx₀
    rw [← hax]; exact addOrderOf_nsmul_eq_zero x

/-- The additive group of a finite near-field, viewed multiplicatively, is elementary abelian for
some prime `f`.  This is the form consumed by Appendix I's `exists_field_semilinear`
(`OddOrder.GroupTheory.IsElementaryAbelian f (Multiplicative F)`). -/
theorem isElementaryAbelian_multiplicative [Finite F] [Nontrivial F] :
    ∃ f : ℕ, f.Prime ∧ OddOrder.GroupTheory.IsElementaryAbelian f (Multiplicative F) := by
  obtain ⟨f, hf, hfx⟩ := exists_prime_char (F := F)
  refine ⟨f, hf, fun x y => mul_comm x y, fun x => ?_⟩
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow, toAdd_one]
  exact hfx (Multiplicative.toAdd x)

/-- The right-multiplication action of a commutative subgroup `A ⊆ Fˣ` on `(F, +)` (written
multiplicatively), as a monoid homomorphism into `MulAut (Multiplicative F)`.  Right multiplication
is additive (`rightMul`); the homomorphism property needs `A` commutative (`hcomm`), since right
multiplication is otherwise only an anti-homomorphism.  Together with `isElementaryAbelian_multiplicative`
this is the data fed to Appendix I's `exists_field_semilinear`. -/
noncomputable def rightMulAction (A : Subgroup Fˣ)
    (hcomm : ∀ u v : A, (u : Fˣ) * (v : Fˣ) = (v : Fˣ) * (u : Fˣ)) :
    A →* MulAut (Multiplicative F) where
  toFun u := (rightMul ((u : Fˣ) : F) (Units.ne_zero _)).toMultiplicative
  map_one' := by
    ext x
    apply Multiplicative.toAdd.injective
    show Multiplicative.toAdd x * (((1 : A) : Fˣ) : F) = Multiplicative.toAdd x
    rw [OneMemClass.coe_one, Units.val_one, mul_one]
  map_mul' u v := by
    ext x
    apply Multiplicative.toAdd.injective
    show Multiplicative.toAdd x * (((u * v : A) : Fˣ) : F)
      = Multiplicative.toAdd x * (((v : Fˣ) : F)) * (((u : Fˣ) : F))
    have hc' : ((u : Fˣ) : F) * ((v : Fˣ) : F) = ((v : Fˣ) : F) * ((u : Fˣ) : F) := by
      rw [← Units.val_mul, ← Units.val_mul, hcomm u v]
    rw [Subgroup.coe_mul, Units.val_mul, hc', ← mul_assoc]

/-- The action of `rightMulAction` on additive coordinates: `u` sends `x` to `x * (u : F)`. -/
@[simp] theorem rightMulAction_toAdd (A : Subgroup Fˣ)
    (hcomm : ∀ u v : A, (u : Fˣ) * (v : Fˣ) = (v : Fˣ) * (u : Fˣ)) (u : A) (x : Multiplicative F) :
    Multiplicative.toAdd (rightMulAction A hcomm u x) = Multiplicative.toAdd x * ((u : Fˣ) : F) :=
  rfl

end NearFieldBasics

variable {G Ω F : Type*} [Group G]

/-- A lightweight carrier for finite near-field structure.  The algebraic laws
are proposition fields until a reusable near-field API is introduced. -/
structure FiniteNearField where
  carrier_nonempty : Nonempty F
  finite : Prop
  finite_holds : finite
  additive_group : Prop
  additive_group_holds : additive_group
  multiplicative_group : Prop
  multiplicative_group_holds : multiplicative_group
  right_distrib : Prop
  right_distrib_holds : right_distrib

/-- **Peterfalvi Appendix C, Proposition 1**: a 2-rank one group satisfying
Suzuki hypotheses (A1)--(A2) is an affine group over a finite near-field. -/
structure RankOneNearFieldData
    (hyp : Suzuki.Hypothesis (G := G) (Ω := Ω)) where
  nearField : FiniteNearField (F := F)
  Sigma : Type*
  affine_model : Prop
  affine_model_holds : affine_model
  Q_identification : Prop
  Q_identification_holds : Q_identification
  D_identification : Prop
  D_identification_holds : D_identification
  unique_involution_in_H : Prop
  unique_involution_in_H_holds : unique_involution_in_H

/-- **Peterfalvi Appendix C, Proposition 1**. -/
theorem rankOne_affine_nearField [Finite G]
    (hyp : Suzuki.Hypothesis (G := G) (Ω := Ω))
    (two_rank_one : Prop) :
    two_rank_one → ∃ data : RankOneNearFieldData (F := F) hyp,
      data.affine_model := by
  sorry

/-- **Peterfalvi Appendix C, Proposition 2**: a finite near-field whose
multiplicative group has a cyclic subgroup of index two is either a field or the
exceptional near-field `F_{r^2,2}`. -/
theorem cyclic_index_two_nearField_classification
    (nearField : FiniteNearField (F := F)) (cyclic_index_two : Prop) :
    cyclic_index_two → ∃ classification : Prop, classification := by
  sorry

end OddOrder.Peterfalvi.Appendices.NearFields
