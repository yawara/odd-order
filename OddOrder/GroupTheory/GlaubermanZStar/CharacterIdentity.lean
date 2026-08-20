/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.Modular.CentralCharacterTrace

/-!
# A class-product identity: `χ(a) χ(b) = c · χ(1)` when `χ` is constant on `cl(a)·cl(b)`

Navarro (7.9), Step 9.  If an irreducible character `χ` takes the *same* value `c` at every
product `x y` with `x` conjugate to `a` and `y` conjugate to `b`, then

`χ(a) · χ(b) = c · χ(1)`.

Equivalently `α(a) α(b) = α(ab)` for `α = χ/χ(1)` when `χ` is constant on the product set — the
form Navarro writes.  Everything here is division-free: the central character satisfies
`ω_χ(Ĉ) χ(1) = |C| χ(a)` (`centralScalar_classSum_mul_character_one_out`) and is multiplicative
on the centre (`centralScalar_mul`), and `Ĉ · D̂` has total coefficient mass `|C| · |D|`.

## Main results

* `OddOrder.RepresentationTheory.Modular.character_mul_eq_of_const_on_class_product`
-/

open Matrix MonoidAlgebra OddOrder.GroupTheory.CenterClassSum OddOrder.RepresentationTheory

namespace OddOrder.RepresentationTheory.Modular

variable {K G : Type*} [Field K] [CharZero K] [Group G] [Fintype G]
  [DecidableEq (ConjClasses G)]
variable {ι' : Type*} {m : ι' → Type*} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
  [∀ i, Nonempty (m i)]
variable (e : MonoidAlgebra K G ≃ₐ[K] ∀ i, Matrix (m i) (m i) K) (i : ι')

open scoped Classical in
/-- The class as a `Finset` filter has the cardinality recorded by `conjugacyClassSize`. -/
theorem card_filter_eq_conjugacyClassSize (C : ConjClasses G) :
    (Finset.univ.filter (fun g : G => ConjClasses.mk g = C)).card = conjugacyClassSize C := by
  classical
  rw [conjugacyClassSize, ← Nat.card_eq_finsetCard]
  refine Nat.card_congr ?_
  exact
    { toFun := fun x => ⟨x, ConjClasses.mem_carrier_iff_mk_eq.mpr (Finset.mem_filter.mp x.2).2⟩
      invFun := fun x => ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        ConjClasses.mem_carrier_iff_mk_eq.mp x.2⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

omit [CharZero K] [∀ i, Nonempty (m i)] in
open scoped Classical in
/-- The total coefficient mass of `Ĉ · w` against a class function that is constant on the
relevant products.  This is the inner computation of `character_mul_eq_of_const_on_class_product`:
reindexing `g = v y` turns `∑_g (Ĉ D̂)(g) χ(g)` into `∑_{v ∈ C} ∑_{y ∈ D} χ(v y)`. -/
theorem sum_coeff_classSum_mul_classSum_mul (C D : ConjClasses G) (c : K)
    (hconst : ∀ x y : G, ConjClasses.mk x = C → ConjClasses.mk y = D →
      (wedderburnRepresentation e i).character (x * y) = c) :
    ∑ g : G, (classSum (k := K) C * classSum (k := K) D).coeff g
        * (wedderburnRepresentation e i).character g
      = (conjugacyClassSize C : K) * ((conjugacyClassSize D : K) * c) := by
  classical
  have hstep : ∀ g : G, (classSum (k := K) C * classSum (k := K) D).coeff g
      = ∑ v ∈ Finset.univ.filter (fun v : G => ConjClasses.mk v = C),
          (classSum (k := K) D).coeff (v⁻¹ * g) := fun g => coeff_classSum_mul C _ g
  calc ∑ g : G, (classSum (k := K) C * classSum (k := K) D).coeff g
          * (wedderburnRepresentation e i).character g
      = ∑ g : G, ∑ v ∈ Finset.univ.filter (fun v : G => ConjClasses.mk v = C),
          (classSum (k := K) D).coeff (v⁻¹ * g)
            * (wedderburnRepresentation e i).character g := by
        refine Finset.sum_congr rfl fun g _ => ?_
        rw [hstep g, Finset.sum_mul]
    _ = ∑ v ∈ Finset.univ.filter (fun v : G => ConjClasses.mk v = C), ∑ g : G,
          (classSum (k := K) D).coeff (v⁻¹ * g)
            * (wedderburnRepresentation e i).character g := Finset.sum_comm
    _ = ∑ v ∈ Finset.univ.filter (fun v : G => ConjClasses.mk v = C),
          ((conjugacyClassSize D : K) * c) := by
        refine Finset.sum_congr rfl fun v hv => ?_
        have hvC : ConjClasses.mk v = C := (Finset.mem_filter.mp hv).2
        -- reindex `g = v * y`
        have hre : ∑ g : G, (classSum (k := K) D).coeff (v⁻¹ * g)
              * (wedderburnRepresentation e i).character g
            = ∑ y : G, (classSum (k := K) D).coeff y
              * (wedderburnRepresentation e i).character (v * y) :=
          (Fintype.sum_equiv (Equiv.mulLeft v) _ _ fun y => by simp).symm
        rw [hre]
        have hterm : ∀ y : G, (classSum (k := K) D).coeff y
              * (wedderburnRepresentation e i).character (v * y)
            = if ConjClasses.mk y = D then c else 0 := by
          intro y
          rw [coeff_classSum]
          by_cases hy : ConjClasses.mk y = D
          · rw [if_pos hy, if_pos hy, one_mul, hconst v y hvC hy]
          · rw [if_neg hy, if_neg hy, zero_mul]
        rw [Finset.sum_congr rfl fun y _ => hterm y, Finset.sum_ite, Finset.sum_const_zero,
          add_zero, Finset.sum_const, nsmul_eq_mul, card_filter_eq_conjugacyClassSize]
    _ = (conjugacyClassSize C : K) * ((conjugacyClassSize D : K) * c) := by
        rw [Finset.sum_const, nsmul_eq_mul, card_filter_eq_conjugacyClassSize]

-- `Fintype G` and `DecidableEq (ConjClasses G)` appear only through the class sums used in the
-- proof, so the linter reports them as proof-only; they are what makes those sums exist.
set_option linter.unusedFintypeInType false in
omit [DecidableEq (ConjClasses G)] in
open scoped Classical in
/-- **Navarro (7.9), Step 9's identity.**  If `χ` takes the constant value `c` at every product
of an element of `cl(a)` with an element of `cl(b)`, then `χ(a) χ(b) = c χ(1)`.

Apply the central character `ω_χ` to `Ĉ · D̂` two ways: multiplicativity plus
`ω_χ(Ĉ) χ(1) = |C| χ(a)` gives `|C| |D| χ(a) χ(b)` on one side, and the coefficient expansion
gives `|C| |D| c χ(1)` on the other. -/
theorem character_mul_eq_of_const_on_class_product (a b : G) (c : K)
    (hconst : ∀ x y : G, ConjClasses.mk x = ConjClasses.mk a →
      ConjClasses.mk y = ConjClasses.mk b →
      (wedderburnRepresentation e i).character (x * y) = c) :
    (wedderburnRepresentation e i).character a * (wedderburnRepresentation e i).character b
      = c * (wedderburnRepresentation e i).character 1 := by
  classical
  have hout : ∀ (E : ConjClasses G) (x : G), ConjClasses.mk x = E →
      (wedderburnRepresentation e i).character E.out
        = (wedderburnRepresentation e i).character x := by
    intro E x hx
    refine character_eq_of_isConj _ (ConjClasses.mk_eq_mk_iff_isConj.mp ?_)
    rw [← ConjClasses.quotient_mk_eq_mk (a := E.out)]
    rw [Quotient.out_eq E, hx]
  have hC : MatrixModule.centralScalar e.toAlgHom.toRingHom i (classSum (ConjClasses.mk a))
        * (wedderburnRepresentation e i).character 1
      = (conjugacyClassSize (ConjClasses.mk a) : K)
        * (wedderburnRepresentation e i).character a := by
    rw [centralScalar_classSum_mul_character_one_out e i (ConjClasses.mk a), hout _ a rfl]
  have hD : MatrixModule.centralScalar e.toAlgHom.toRingHom i (classSum (ConjClasses.mk b))
        * (wedderburnRepresentation e i).character 1
      = (conjugacyClassSize (ConjClasses.mk b) : K)
        * (wedderburnRepresentation e i).character b := by
    rw [centralScalar_classSum_mul_character_one_out e i (ConjClasses.mk b), hout _ b rfl]
  have hprod : MatrixModule.centralScalar e.toAlgHom.toRingHom i (classSum (ConjClasses.mk a))
        * MatrixModule.centralScalar e.toAlgHom.toRingHom i (classSum (ConjClasses.mk b))
        * (wedderburnRepresentation e i).character 1
      = (conjugacyClassSize (ConjClasses.mk a) : K)
        * ((conjugacyClassSize (ConjClasses.mk b) : K) * c) := by
    rw [← centralScalar_mul e i (classSum_mem_center (ConjClasses.mk a))
        (classSum_mem_center (ConjClasses.mk b)),
      centralScalar_mul_character_one e i _
        (Subalgebra.mul_mem _ (classSum_mem_center (ConjClasses.mk a))
          (classSum_mem_center (ConjClasses.mk b)))]
    exact sum_coeff_classSum_mul_classSum_mul e i (ConjClasses.mk a) (ConjClasses.mk b) c hconst
  have hkey : (conjugacyClassSize (ConjClasses.mk a) : K)
        * (conjugacyClassSize (ConjClasses.mk b) : K)
        * ((wedderburnRepresentation e i).character a
          * (wedderburnRepresentation e i).character b)
      = (conjugacyClassSize (ConjClasses.mk a) : K)
        * (conjugacyClassSize (ConjClasses.mk b) : K)
        * (c * (wedderburnRepresentation e i).character 1) := by
    calc (conjugacyClassSize (ConjClasses.mk a) : K)
          * (conjugacyClassSize (ConjClasses.mk b) : K)
          * ((wedderburnRepresentation e i).character a
            * (wedderburnRepresentation e i).character b)
        = ((conjugacyClassSize (ConjClasses.mk a) : K)
            * (wedderburnRepresentation e i).character a)
          * ((conjugacyClassSize (ConjClasses.mk b) : K)
            * (wedderburnRepresentation e i).character b) := by ring
      _ = (MatrixModule.centralScalar e.toAlgHom.toRingHom i (classSum (ConjClasses.mk a))
            * (wedderburnRepresentation e i).character 1)
          * (MatrixModule.centralScalar e.toAlgHom.toRingHom i (classSum (ConjClasses.mk b))
            * (wedderburnRepresentation e i).character 1) := by rw [hC, hD]
      _ = (MatrixModule.centralScalar e.toAlgHom.toRingHom i (classSum (ConjClasses.mk a))
            * MatrixModule.centralScalar e.toAlgHom.toRingHom i (classSum (ConjClasses.mk b))
            * (wedderburnRepresentation e i).character 1)
          * (wedderburnRepresentation e i).character 1 := by ring
      _ = ((conjugacyClassSize (ConjClasses.mk a) : K)
            * ((conjugacyClassSize (ConjClasses.mk b) : K) * c))
          * (wedderburnRepresentation e i).character 1 := by rw [hprod]
      _ = (conjugacyClassSize (ConjClasses.mk a) : K)
          * (conjugacyClassSize (ConjClasses.mk b) : K)
          * (c * (wedderburnRepresentation e i).character 1) := by ring
  refine mul_left_cancel₀ (mul_ne_zero ?_ ?_) hkey
  · exact Nat.cast_ne_zero.mpr (conjugacyClassSize_pos (ConjClasses.mk a)).ne'
  · exact Nat.cast_ne_zero.mpr (conjugacyClassSize_pos (ConjClasses.mk b)).ne'

end OddOrder.RepresentationTheory.Modular
