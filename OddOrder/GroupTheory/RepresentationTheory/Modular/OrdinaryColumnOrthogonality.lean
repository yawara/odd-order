/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.SecondOrthogonality
import OddOrder.GroupTheory.RepresentationTheory.Modular.OrdinaryIrrCount

/-!
# Second (column) orthogonality over a splitting field

Navarro (2.13) reads the first orthogonality relation *down the columns* of the character table:

`∑_{χ ∈ Irr(G)} χ(x) χ(y⁻¹) = |C_G(x)|` if `x ~ y`, and `0` otherwise.

Over `ℂ` this is `RepresentationTheory/ColumnOrthogonality`; over the splitting field `K` of a
`p`-modular system it has to be redone, since there is no complex conjugation available and the
irreducibles are the Wedderburn blocks of `K[G]`.

The argument is the classical one.  Collecting the first orthogonality relation
(`sum_character_mul_character_inv`) by conjugacy classes turns it into a matrix identity
`X · W = 1`, where `X` is the character table and `W` is the table of inverse-evaluated characters
weighted by `|C| / |G|`.  Because the table is **square**
(`card_eq_card_conjClasses`), a one-sided inverse is two-sided, and `W · X = 1` is exactly the
column relation.

## Main results

* `OddOrder.RepresentationTheory.Modular.sum_eq_sum_conjClasses` — a class function summed over
  `G` is the class-size-weighted sum over `cl(G)`
* `OddOrder.RepresentationTheory.Modular.characterMatrix_mul_characterMatrixInv` — `X · W = 1`
* `OddOrder.RepresentationTheory.Modular.characterMatrixInv_mul_characterMatrix` — `W · X = 1`
* `OddOrder.RepresentationTheory.Modular.sum_character_inv_mul_character_classRep` — the column
  relation itself, on class representatives
* `OddOrder.RepresentationTheory.Modular.sum_character_inv_mul_character` — the same for
  arbitrary elements
-/

namespace OddOrder.RepresentationTheory.Modular

open Module OddOrder.RepresentationTheory

/-! ### Summing a class function by conjugacy classes -/

variable {G : Type*} [Group G]

/-- **A class function summed over `G` is the class-size-weighted sum over `cl(G)`.**  Split `G`
into its conjugacy classes and use that the summand is constant on each. -/
theorem sum_eq_sum_conjClasses {M : Type*} [AddCommMonoid M] [Fintype G]
    [Fintype (ConjClasses G)] (f : G → M) (hf : ∀ g h : G, IsConj g h → f g = f h) :
    ∑ g : G, f g
      = ∑ C : ConjClasses G, conjugacyClassSize C • f (conjugacyClassRepresentative C) := by
  classical
  letI : ∀ C : ConjClasses G, Fintype C.carrier := fun _ => Fintype.ofFinite _
  rw [← Fintype.sum_equiv conjClassesSigmaCarrierEquiv (fun x => f x.2.1) f fun _ => rfl,
    Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun C _ => ?_
  have hconst : ∀ x : C.carrier, f x.1 = f (conjugacyClassRepresentative C) := by
    intro x
    refine hf _ _ (ConjClasses.mk_eq_mk_iff_isConj.mp ?_)
    rw [ConjClasses.mem_carrier_iff_mk_eq.mp x.2, conjugacyClassRepresentative_mk_eq]
  rw [Finset.sum_congr rfl fun x _ => hconst x, Finset.sum_const, Finset.card_univ]
  congr 1
  rw [conjugacyClassSize, Nat.card_eq_fintype_card]

/-- **A class function is constant on a conjugacy class**, so its sum over any `Finset` cut out
by conjugacy to `w` is `#t • f w`. -/
theorem sum_eq_card_smul_of_forall_isConj {M : Type*} [AddCommMonoid M] (f : G → M)
    (hf : ∀ a b : G, IsConj a b → f a = f b) (w : G) (t : Finset G)
    (ht : ∀ z : G, z ∈ t ↔ IsConj z w) :
    ∑ z ∈ t, f z = t.card • f w := by
  rw [Finset.sum_congr rfl fun z hz => hf z w ((ht z).mp hz), Finset.sum_const]

/-- **`|class(w)| · |C_G(w)| = |G|`**, for the conjugacy class presented as an arbitrary `Finset`
cut out by conjugacy to `w`. -/
theorem card_mul_card_centralizer_of_forall_isConj [Finite G] (w : G) (t : Finset G)
    (ht : ∀ z : G, z ∈ t ↔ IsConj z w) :
    t.card * Nat.card ↥(Subgroup.centralizer ({w} : Set G)) = Nat.card G := by
  rw [← conjugacyClassSize_mk_mul_card_centralizer (G := G) w]
  congr 1
  rw [conjugacyClassSize, ← Nat.card_eq_finsetCard]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun z => (ht z).trans
    (ConjClasses.mem_carrier_iff_mk_eq.trans ConjClasses.mk_eq_mk_iff_isConj).symm)

/-- The size of a conjugacy class is invertible in `K`: it divides `|G|`, which is. -/
theorem isUnit_conjugacyClassSize {K : Type*} [Field K] [Finite G]
    [Invertible (Nat.card G : K)] (C : ConjClasses G) :
    IsUnit ((conjugacyClassSize C : K)) := by
  obtain ⟨g, rfl⟩ := ConjClasses.exists_rep C
  have hprod : (conjugacyClassSize (ConjClasses.mk g) : K)
      * (Nat.card (Subgroup.centralizer ({g} : Set G)) : K) = (Nat.card G : K) := by
    exact_mod_cast congrArg (Nat.cast : ℕ → K)
      (conjugacyClassSize_mk_mul_card_centralizer (G := G) g)
  refine isUnit_of_mul_isUnit_left (y := (Nat.card (Subgroup.centralizer ({g} : Set G)) : K)) ?_
  rw [hprod]
  exact isUnit_of_invertible _

/-- **Conjugate elements have centralizers of the same size.**  Their conjugacy classes coincide,
and `|C| · |C_G(x)| = |G|` with `|C| > 0`. -/
theorem card_centralizer_eq_of_isConj [Finite G] {x y : G} (h : IsConj x y) :
    Nat.card (Subgroup.centralizer ({x} : Set G))
      = Nat.card (Subgroup.centralizer ({y} : Set G)) := by
  have hmk : ConjClasses.mk x = ConjClasses.mk y := ConjClasses.mk_eq_mk_iff_isConj.mpr h
  have hx := conjugacyClassSize_mk_mul_card_centralizer (G := G) x
  have hy := conjugacyClassSize_mk_mul_card_centralizer (G := G) y
  rw [hmk] at hx
  exact Nat.eq_of_mul_eq_mul_left (conjugacyClassSize_pos _) (hx.trans hy.symm)

/-- **Inverses of conjugate elements are conjugate.** -/
theorem IsConj.inv' {x y : G} (h : IsConj x y) : IsConj x⁻¹ y⁻¹ := by
  obtain ⟨u, hu⟩ := h
  have hh : (u : G) * x * ((u : G))⁻¹ = y := by rw [hu.eq]; group
  exact ⟨u, by rw [SemiconjBy, ← hh]; group⟩

/-- **Characters are class functions.** -/
theorem character_eq_of_isConj {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (ρ : Representation K G V) {x y : G} (h : IsConj x y) : ρ.character x = ρ.character y := by
  obtain ⟨u, hu⟩ := h
  have hh : (u : G) * x * ((u : G))⁻¹ = y := by rw [hu.eq]; group
  rw [← hh, Representation.char_conj]

/-! ### The character table as a square matrix -/

variable {K : Type*} [Field K] {ι' : Type*} {m : ι' → Type*}
  [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] [∀ i, Nonempty (m i)]
  (e : MonoidAlgebra K G ≃ₐ[K] ∀ j, Matrix (m j) (m j) K)
  [Fintype G] [Fintype (ConjClasses G)] [Fintype ι'] [DecidableEq ι']
  [Invertible (Nat.card G : K)]

/-- A representative of the conjugacy class matched with the index `j` by
`equivConjClasses`. -/
noncomputable def classRep (j : ι') : G :=
  conjugacyClassRepresentative (equivConjClasses e j)

/-- **The character table**: rows are the ordinary irreducibles, columns the conjugacy classes
(transported to `ι'` by `equivConjClasses`). -/
noncomputable def characterMatrix : Matrix ι' ι' K := fun i j =>
  (wedderburnRepresentation e i).character (classRep e j)

/-- The candidate inverse of the character table: characters evaluated at inverses, weighted by
`|C| / |G|`.  First orthogonality says it *is* the inverse. -/
noncomputable def characterMatrixInv : Matrix ι' ι' K := fun j i =>
  (conjugacyClassSize (equivConjClasses e j) : K) * (Nat.card G : K)⁻¹ *
    (wedderburnRepresentation e i).character (classRep e j)⁻¹

/-- **First orthogonality, collected by classes**: `X · W = 1`. -/
theorem characterMatrix_mul_characterMatrixInv :
    characterMatrix e * characterMatrixInv e = 1 := by
  ext i i'
  have hclass : ∀ g h : G, IsConj g h →
      (wedderburnRepresentation e i).character g
        * (wedderburnRepresentation e i').character g⁻¹
      = (wedderburnRepresentation e i).character h
        * (wedderburnRepresentation e i').character h⁻¹ := by
    rintro g h ⟨u, hu⟩
    have hh : (u : G) * g * ((u : G))⁻¹ = h := by rw [hu.eq]; group
    rw [← hh, ← Representation.char_conj (wedderburnRepresentation e i) g (u : G),
      show ((u : G) * g * ((u : G))⁻¹)⁻¹ = (u : G) * g⁻¹ * ((u : G))⁻¹ by group,
      ← Representation.char_conj (wedderburnRepresentation e i') g⁻¹ (u : G)]
  have hsum := sum_eq_sum_conjClasses
    (fun g : G => (wedderburnRepresentation e i).character g
      * (wedderburnRepresentation e i').character g⁻¹) hclass
  rw [sum_character_mul_character_inv e i' i] at hsum
  -- rewrite the class sum through `equivConjClasses`
  rw [← Equiv.sum_comp (equivConjClasses e)] at hsum
  have hunit : ((Nat.card G : K)) ≠ 0 := (isUnit_of_invertible (Nat.card G : K)).ne_zero
  rw [Matrix.mul_apply, Matrix.one_apply]
  have hexp : ∀ j : ι', characterMatrix e i j * characterMatrixInv e j i'
      = (Nat.card G : K)⁻¹ * (conjugacyClassSize (equivConjClasses e j) •
        ((wedderburnRepresentation e i).character
            (conjugacyClassRepresentative (equivConjClasses e j))
          * (wedderburnRepresentation e i').character
            (conjugacyClassRepresentative (equivConjClasses e j))⁻¹)) := by
    intro j
    simp only [characterMatrix, characterMatrixInv, classRep, nsmul_eq_mul]
    ring
  rw [Finset.sum_congr rfl fun j _ => hexp j, ← Finset.mul_sum, ← hsum]
  split
  · next h => rw [if_pos (by rw [h]), inv_mul_cancel₀ hunit]
  · next h => rw [if_neg (fun hc => h hc.symm), mul_zero]

/-- **Second (column) orthogonality, in matrix form**: `W · X = 1`.  The character table is square,
so the one-sided inverse of `characterMatrix_mul_characterMatrixInv` is two-sided. -/
theorem characterMatrixInv_mul_characterMatrix :
    characterMatrixInv e * characterMatrix e = 1 :=
  mul_eq_one_comm.mp (characterMatrix_mul_characterMatrixInv e)

/-- **Second (column) orthogonality, on class representatives.**  Reading `W · X = 1` entrywise
and clearing the weight `|C| / |G|` gives `∑_χ χ(x⁻¹) χ(y) = |C_G(x)| δ`. -/
theorem sum_character_inv_mul_character_classRep (j j' : ι') :
    ∑ i : ι', (wedderburnRepresentation e i).character (classRep e j)⁻¹
        * (wedderburnRepresentation e i).character (classRep e j')
      = if j = j' then
          (Nat.card (Subgroup.centralizer ({classRep e j} : Set G)) : K) else 0 := by
  have hmul := congrFun (congrFun (characterMatrixInv_mul_characterMatrix e) j) j'
  rw [Matrix.mul_apply, Matrix.one_apply] at hmul
  have hcent : (conjugacyClassSize (equivConjClasses e j) : K)
      * (Nat.card (Subgroup.centralizer ({classRep e j} : Set G)) : K) = (Nat.card G : K) := by
    have hrep : ConjClasses.mk (classRep e j) = equivConjClasses e j :=
      conjugacyClassRepresentative_mk_eq _
    have := conjugacyClassSize_mk_mul_card_centralizer (G := G) (classRep e j)
    rw [hrep] at this
    exact_mod_cast congrArg (Nat.cast : ℕ → K) this
  have hunit : ((Nat.card G : K)) ≠ 0 := (isUnit_of_invertible (Nat.card G : K)).ne_zero
  have hexp : ∀ i : ι', characterMatrixInv e j i * characterMatrix e i j'
      = ((conjugacyClassSize (equivConjClasses e j) : K) * (Nat.card G : K)⁻¹) *
        ((wedderburnRepresentation e i).character (classRep e j)⁻¹
          * (wedderburnRepresentation e i).character (classRep e j')) := by
    intro i
    simp only [characterMatrix, characterMatrixInv]
    ring
  rw [Finset.sum_congr rfl fun i _ => hexp i, ← Finset.mul_sum] at hmul
  set S := ∑ i : ι', (wedderburnRepresentation e i).character (classRep e j)⁻¹
    * (wedderburnRepresentation e i).character (classRep e j') with hS
  have hkey : (conjugacyClassSize (equivConjClasses e j) : K) * S
      = (Nat.card G : K) * (if j = j' then (1 : K) else 0) := by
    rw [← hmul]; field_simp
  have hcs := isUnit_conjugacyClassSize (K := K) (equivConjClasses e j)
  refine hcs.mul_left_cancel ?_
  rw [hkey, ← hcent]
  rcases eq_or_ne j j' with h | h <;> simp [h]

omit [Fintype (ConjClasses G)] [DecidableEq ι'] in
open scoped Classical in
/-- **Second (column) orthogonality over the splitting field**, for arbitrary elements:

`∑_{χ ∈ Irr(G)} χ(x⁻¹) χ(y) = |C_G(x)|` if `x ~ y`, and `0` otherwise.

Transport `sum_character_inv_mul_character_classRep` along the conjugacies `x ~ classRep j`,
`y ~ classRep j'`, using that characters are class functions and that conjugate elements have
equinumerous centralizers. -/
theorem sum_character_inv_mul_character (x y : G) :
    ∑ i : ι', (wedderburnRepresentation e i).character x⁻¹
        * (wedderburnRepresentation e i).character y
      = if IsConj x y then (Nat.card (Subgroup.centralizer ({x} : Set G)) : K) else 0 := by
  classical
  letI : DecidableEq ι' := Classical.decEq ι'
  letI : Fintype (ConjClasses G) := Fintype.ofFinite _
  set j := (equivConjClasses e).symm (ConjClasses.mk x) with hj
  set j' := (equivConjClasses e).symm (ConjClasses.mk y) with hj'
  have hxc : IsConj x (classRep e j) := by
    refine ConjClasses.mk_eq_mk_iff_isConj.mp ?_
    rw [classRep, conjugacyClassRepresentative_mk_eq, hj, Equiv.apply_symm_apply]
  have hyc : IsConj y (classRep e j') := by
    refine ConjClasses.mk_eq_mk_iff_isConj.mp ?_
    rw [classRep, conjugacyClassRepresentative_mk_eq, hj', Equiv.apply_symm_apply]
  have hrw : ∀ i : ι', (wedderburnRepresentation e i).character x⁻¹
      * (wedderburnRepresentation e i).character y
      = (wedderburnRepresentation e i).character (classRep e j)⁻¹
        * (wedderburnRepresentation e i).character (classRep e j') := fun i => by
    rw [character_eq_of_isConj _ (IsConj.inv' hxc), character_eq_of_isConj _ hyc]
  rw [Finset.sum_congr rfl fun i _ => hrw i, sum_character_inv_mul_character_classRep,
    card_centralizer_eq_of_isConj hxc]
  have hiff : (j = j') ↔ IsConj x y := by
    rw [hj, hj', Equiv.symm_apply_eq, Equiv.apply_symm_apply, ConjClasses.mk_eq_mk_iff_isConj]
  by_cases h : IsConj x y
  · rw [if_pos (hiff.mpr h), if_pos h]
  · rw [if_neg (fun hc => h (hiff.mp hc)), if_neg h]

end OddOrder.RepresentationTheory.Modular
