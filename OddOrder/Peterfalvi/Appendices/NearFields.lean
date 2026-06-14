/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki
import OddOrder.Peterfalvi.Appendices.SemilinearField

/-!
# Peterfalvi Appendix C: On Near-Fields

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Appendix C, pp. 137--138.

The appendix uses finite near-fields to describe the 2-rank one case of the
Suzuki theorem and records the special Zassenhaus classification needed there.
-/

namespace OddOrder.Peterfalvi.Appendices.NearFields
-- scaffold opaque-Prop convention: see notes/meta/scaffold_opaque_prop_convention.md

/-- **A finite group acting freely on a finite type divides its cardinality**: if every stabilizer
is trivial, then `|G| ∣ |α|` (each orbit has size `|G|`, and the orbits partition `α`).  General
group-action fact (could live in `Mathlib.GroupTheory.GroupAction`); used here for the orbit
counting `|A| ∣ |U| - 1` in Appendix C, Proposition 2. -/
theorem card_group_dvd_card_of_free {G β : Type*} [Group G] [MulAction G β]
    [Finite G] [Finite β] (hfree : ∀ b : β, MulAction.stabilizer G b = ⊥) :
    Nat.card G ∣ Nat.card β := by
  classical
  haveI : Fintype (MulAction.orbitRel.Quotient G β) := Fintype.ofFinite _
  rw [Nat.card_congr (MulAction.selfEquivSigmaOrbits G β), Nat.card_sigma]
  refine Finset.dvd_sum fun ω _ => ?_
  have hc : Nat.card (MulAction.orbit G ω.out) = Nat.card G := by
    rw [Nat.card_congr (MulAction.orbitEquivQuotientStabilizer G ω.out), hfree ω.out,
      ← Subgroup.index_eq_card, Subgroup.index_bot]
  exact ⟨1, by rw [hc, mul_one]⟩

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

/-- `A ⊆ Fˣ` acts **freely** on `F^#` by right multiplication: a nontrivial element fixes no
nonzero point (group cancellation in the group-with-zero `F`).  This is the input to the orbit
counting that shows the index-2 subgroup `A` acts irreducibly. -/
theorem rightMulAction_eq_self_iff (A : Subgroup Fˣ)
    (hcomm : ∀ u v : A, (u : Fˣ) * (v : Fˣ) = (v : Fˣ) * (u : Fˣ)) (a : A) (x : Multiplicative F)
    (hx : x ≠ 1) (hfix : rightMulAction A hcomm a x = x) : a = 1 := by
  have h1 : Multiplicative.toAdd x * ((a : Fˣ) : F) = Multiplicative.toAdd x := by
    have h := congrArg Multiplicative.toAdd hfix
    rwa [rightMulAction_toAdd] at h
  have hx0 : Multiplicative.toAdd x ≠ 0 := fun h =>
    hx (Multiplicative.toAdd.injective (h.trans toAdd_one.symm))
  have hval : ((a : Fˣ) : F) = 1 := mul_left_cancel₀ hx0 (by rw [h1, mul_one])
  exact OneMemClass.coe_eq_one.mp (Units.val_eq_one.mp hval)

/-- Any subgroup `A ⊆ Fˣ` has order coprime to `|F|`: `|A| ∣ |Fˣ| = |F| - 1` (Lagrange), and
consecutive integers are coprime.  This is the coprimality hypothesis needed for Maschke's theorem
when splitting an `A`-invariant subgroup of `(F, +)`. -/
theorem card_coprime (A : Subgroup Fˣ) [Finite F] :
    Nat.Coprime (Nat.card A) (Nat.card F) := by
  haveI : Nonempty F := ⟨0⟩
  have h1 : Nat.card A ∣ Nat.card Fˣ := Subgroup.card_subgroup_dvd_card A
  rw [Nat.card_units] at h1
  have hcop : ∀ n : ℕ, 0 < n → Nat.Coprime (n - 1) n := by
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [Nat.add_sub_cancel, Nat.add_comm]
    exact Nat.coprime_add_self_right.mpr (Nat.coprime_one_right m)
  exact Nat.Coprime.coprime_dvd_left h1 (hcop (Nat.card F) Nat.card_pos)

/-- If `A ⊆ Fˣ` has index `2`, then `|F| = 2|A| + 1` (`|A| · index = |Fˣ| = |F| - 1`).  This is the
cardinality identity behind the `(|A|+1)² > 2|A|+1` contradiction proving `A` acts irreducibly. -/
theorem card_eq_of_index_two (A : Subgroup Fˣ) [Finite F] (hidx : A.index = 2) :
    Nat.card F = 2 * Nat.card A + 1 := by
  haveI : Nonempty F := ⟨0⟩
  have h := Subgroup.card_mul_index A
  rw [hidx, Nat.card_units] at h
  have hpos : 0 < Nat.card F := Nat.card_pos
  omega

/-- **Near-field field structure** (the first half of Peterfalvi Appendix C, Proposition 2, via
Appendix I Proposition 2).  If a commutative subgroup `A ⊆ Fˣ` of a finite near-field acts
*irreducibly* on `(F, +)` by right multiplication, then `(F, +)` is a `1`-dimensional vector space
over a finite field `K` with `|K| = |F|` (i.e. `F` carries a field structure refining its additive
group).  Obtained by feeding the near-field data — `isElementaryAbelian_multiplicative` and
`rightMulAction` — into `exists_field_semilinear`. -/
theorem nearField_field_structure.{u} {F : Type u} [NearField F] [Finite F] [Nontrivial F]
    (A : Subgroup Fˣ)
    (hcomm : ∀ u v : A, (u : Fˣ) * (v : Fˣ) = (v : Fˣ) * (u : Fˣ))
    (hirr : ∀ U : Subgroup (Multiplicative F),
      OddOrder.Isaacs.Ch03.IsAInvariant (rightMulAction A hcomm) U → U = ⊥ ∨ U = ⊤) :
    ∃ (K : Type u) (_ : Field K) (_ : Module K F) (_ : Finite K),
      Module.finrank K F = 1 ∧ Nat.card K = Nat.card F := by
  obtain ⟨f, hf, hE⟩ := isElementaryAbelian_multiplicative (F := F)
  haveI : Fact f.Prime := ⟨hf⟩
  letI : CommGroup A := { (inferInstance : Group A) with
    mul_comm := fun u v => Subtype.ext (by simpa [Subgroup.coe_mul] using hcomm u v) }
  obtain ⟨K, hK, hMod, hKfin, hrank, hcard, _⟩ :=
    OddOrder.Peterfalvi.Appendices.Huppert.exists_field_semilinear (E := Multiplicative F) hE
      (rightMulAction A hcomm) hirr
  exact ⟨K, hK, hMod, hKfin, hrank, hcard⟩

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
