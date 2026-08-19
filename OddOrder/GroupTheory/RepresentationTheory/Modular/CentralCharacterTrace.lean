/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.RepresentationTheory.Character
import OddOrder.GroupTheory.RepresentationTheory.CenterClassSumBasis
import OddOrder.GroupTheory.RepresentationTheory.Modular.OrdinaryColumnOrthogonality
import OddOrder.GroupTheory.RepresentationTheory.SecondOrthogonality

/-!
# The central character of a class sum, read off the character

For a Wedderburn splitting `e : K[G] ≃ₐ[K] ∏_i M_{m_i}(K)` the class sum `K̂` is central, so it
acts on the `i`-th block by a scalar `ω_i(K̂)`.  Taking traces of `e(K̂)_i = ω_i(K̂) · 1` in the two
obvious ways gives the classical

`ω_i(K̂) · χ_i(1) = ∑_{g ∈ K} χ_i(g)  ( = |K| · χ_i(x_K) )`.

This is the only new ingredient needed to run Burnside's class-multiplication formula in the
`K`-Wedderburn setting: combined with the second orthogonality relation it inverts
`ω_i(K̂) ω_i(L̂) = ∑_M a_{KLM} ω_i(M̂)` into a formula for the structure constants `a_{KLM}`, which
is what Navarro (4.19) — and through it Külshammer's formula (6.14) and the third main theorem —
runs on.

## Main results

* `OddOrder.RepresentationTheory.Modular.trace_apply_single` — `χ_i(g)` is the matrix trace
* `OddOrder.RepresentationTheory.Modular.centralScalar_mul_character_one` — for any central `w`
* `OddOrder.RepresentationTheory.Modular.centralScalar_classSum_mul_character_one`
* `OddOrder.RepresentationTheory.Modular.centralScalar_classSum_mul_character_one_out` —
  `ω_i(K̂) χ_i(1) = |K| χ_i(x_K)`
* `OddOrder.RepresentationTheory.Modular.centralScalar_mul` — multiplicativity on the centre
* `OddOrder.RepresentationTheory.Modular.sum_centralScalar_mul_character_eq_card_mul_coeff` —
  Burnside's class-multiplication formula
-/

namespace OddOrder.RepresentationTheory.Modular

open Matrix MonoidAlgebra OddOrder.GroupTheory.CenterClassSum

variable {K G : Type*} [Field K] [Group G] [Fintype G] [DecidableEq (ConjClasses G)]
variable {ι' : Type*} {m : ι' → Type*} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
  [∀ i, Nonempty (m i)]
variable (e : MonoidAlgebra K G ≃ₐ[K] ∀ i, Matrix (m i) (m i) K) (i : ι')

omit [Fintype G] [DecidableEq (ConjClasses G)] [∀ i, Nonempty (m i)] in
/-- The character value `χ_i(g)` is the trace of the matrix `e(g)_i`. -/
theorem trace_apply_single (g : G) :
    (wedderburnRepresentation e i).character g = Matrix.trace (e (MonoidAlgebra.single g 1) i) := by
  classical
  rw [Representation.character]
  have hmap : (wedderburnRepresentation e i) g
      = Matrix.toLin (Pi.basisFun K (m i)) (Pi.basisFun K (m i)) (e (MonoidAlgebra.single g 1) i) :=
    LinearMap.ext fun v => by
      rw [wedderburnRepresentation_apply, Matrix.toLin_apply]
      funext a
      simp [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.single_apply, mul_comm]
  rw [hmap, Matrix.trace_toLin_eq]

omit [Group G] [DecidableEq (ConjClasses G)] [∀ i, Nonempty (m i)] in
/-- Every element of a group algebra over a finite group is the sum of its coefficient
monomials. -/
theorem eq_sum_single (w : MonoidAlgebra K G) :
    w = ∑ g : G, MonoidAlgebra.single g (w.coeff g) := by
  classical
  refine MonoidAlgebra.coeff_injective (Finsupp.ext fun x => ?_)
  rw [MonoidAlgebra.coeff_finsetSum]
  rw [Finset.sum_congr rfl fun g (_ : g ∈ Finset.univ) =>
    show (MonoidAlgebra.single g (w.coeff g)).coeff x
        = if g = x then w.coeff g else 0 by
      rw [MonoidAlgebra.coeff_single, Finsupp.single_apply]]
  rw [Finset.sum_ite_eq' Finset.univ x fun g => w.coeff g]
  simp

omit [DecidableEq (ConjClasses G)] in
/-- **`ω_i(w) · χ_i(1) = ∑_g w(g) χ_i(g)`** for a central `w`.  Both sides are the trace of
`e(w)_i`: on the left because `w` is central and so acts by a scalar, on the right by
linearity. -/
theorem centralScalar_mul_character_one (w : MonoidAlgebra K G)
    (hw : w ∈ Subalgebra.center K (MonoidAlgebra K G)) :
    MatrixModule.centralScalar e.toAlgHom.toRingHom i w
        * (wedderburnRepresentation e i).character 1
      = ∑ g : G, w.coeff g * (wedderburnRepresentation e i).character g := by
  classical
  have hscal : e w i
      = Matrix.scalar (m i) (MatrixModule.centralScalar e.toAlgHom.toRingHom i w) :=
    MatrixModule.scalar_centralScalar e.toAlgHom.toRingHom i e.surjective
      (Semigroup.mem_center_iff.mpr (Subalgebra.mem_center_iff.mp hw))
  have hleft : Matrix.trace (e w i)
      = MatrixModule.centralScalar e.toAlgHom.toRingHom i w
        * (wedderburnRepresentation e i).character 1 := by
    rw [hscal, Representation.char_one, Module.finrank_fintype_fun_eq_card, Matrix.trace,
      Matrix.scalar]
    simp [Matrix.diag_apply, Finset.card_univ, mul_comm]
  have hright : Matrix.trace (e w i)
      = ∑ g : G, w.coeff g * (wedderburnRepresentation e i).character g := by
    conv_lhs => rw [eq_sum_single w]
    rw [map_sum, Finset.sum_apply, Matrix.trace_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [show (MonoidAlgebra.single g (w.coeff g) : MonoidAlgebra K G)
        = w.coeff g • MonoidAlgebra.single g (1 : K) by
      rw [MonoidAlgebra.smul_single, smul_eq_mul, mul_one], map_smul, Pi.smul_apply,
      Matrix.trace_smul, trace_apply_single, smul_eq_mul]
  rw [← hleft, hright]

/-- **`ω_i(K̂) · χ_i(1) = ∑_{g ∈ K} χ_i(g)`.**  The class-sum case of
`centralScalar_mul_character_one`. -/
theorem centralScalar_classSum_mul_character_one (C : ConjClasses G) :
    MatrixModule.centralScalar e.toAlgHom.toRingHom i (classSum C)
        * (wedderburnRepresentation e i).character 1
      = ∑ g : G,
        if ConjClasses.mk g = C then (wedderburnRepresentation e i).character g else 0 := by
  classical
  rw [centralScalar_mul_character_one e i _ (classSum_mem_center C)]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [coeff_classSum]
  by_cases h : ConjClasses.mk g = C
  · rw [if_pos h, if_pos h, one_mul]
  · rw [if_neg h, if_neg h, zero_mul]

open scoped Classical in
set_option backward.isDefEq.respectTransparency false in
/-- **`ω_i(K̂) · χ_i(1) = |K| · χ_i(x_K)`.**  The character is constant on the class, so the sum
`∑_{g ∈ K} χ_i(g)` is `|K|` copies of its value at a representative.  This is the form in which
Navarro's `p^{a-d(K)}` normalisation extracts the `p`-part of `|K|`. -/
theorem centralScalar_classSum_mul_character_one_out (C : ConjClasses G) :
    MatrixModule.centralScalar e.toAlgHom.toRingHom i (classSum C)
        * (wedderburnRepresentation e i).character 1
      = (OddOrder.RepresentationTheory.conjugacyClassSize C : K)
        * (wedderburnRepresentation e i).character C.out := by
  classical
  rw [centralScalar_classSum_mul_character_one e i C]
  have hmk : ConjClasses.mk C.out = C := by
    rw [← ConjClasses.quotient_mk_eq_mk, Quotient.out_eq]
  have hterm : ∀ g : G,
      (if ConjClasses.mk g = C then (wedderburnRepresentation e i).character g else 0)
        = if ConjClasses.mk g = C then (wedderburnRepresentation e i).character C.out else 0 := by
    intro g
    by_cases hg : ConjClasses.mk g = C
    · rw [if_pos hg, if_pos hg]
      exact character_eq_of_isConj (wedderburnRepresentation e i)
        (ConjClasses.mk_eq_mk_iff_isConj.mp (hg.trans hmk.symm))
    · rw [if_neg hg, if_neg hg]
  rw [Finset.sum_congr rfl fun g _ => hterm g, Finset.sum_ite, Finset.sum_const_zero, add_zero,
    Finset.sum_const, nsmul_eq_mul]
  congr 1
  have hcard : (Finset.univ.filter (fun g : G => ConjClasses.mk g = C)).card
      = OddOrder.RepresentationTheory.conjugacyClassSize C := by
    rw [OddOrder.RepresentationTheory.conjugacyClassSize, Nat.card_eq_fintype_card,
      ← Set.toFinset_card]
    refine congrArg Finset.card (Finset.ext fun g => ?_)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_toFinset,
      ConjClasses.mem_carrier_iff_mk_eq]
  rw [hcard]

/-! ### Burnside's class-multiplication formula -/

section Burnside

variable [Fintype ι'] [Invertible (Nat.card G : K)]

omit [Fintype G] [DecidableEq (ConjClasses G)] [Fintype ι'] [Invertible (Nat.card G : K)] in
/-- The central character is multiplicative on central elements. -/
theorem centralScalar_mul {a b : MonoidAlgebra K G}
    (ha : a ∈ Subalgebra.center K (MonoidAlgebra K G))
    (hb : b ∈ Subalgebra.center K (MonoidAlgebra K G)) :
    MatrixModule.centralScalar e.toAlgHom.toRingHom i (a * b)
      = MatrixModule.centralScalar e.toAlgHom.toRingHom i a
        * MatrixModule.centralScalar e.toAlgHom.toRingHom i b := by
  have hlin : ∀ (c : K) (x : MonoidAlgebra K G),
      e.toAlgHom.toRingHom (c • x) = c • e.toAlgHom.toRingHom x := fun c x => by
    change e (c • x) = c • e x
    rw [map_smul]
  have := (MatrixModule.centralCharacterAlg e.toAlgHom.toRingHom i e.surjective hlin).map_mul
    ⟨a, ha⟩ ⟨b, hb⟩
  exact this

set_option maxHeartbeats 800000 in
-- Swapping the two sums and applying column orthogonality termwise.
/-- **Burnside's class-multiplication formula**, in division-free form: for classes `C`, `D` and
any `z ∈ G`,

`∑_i ω_i(Ĉ) ω_i(D̂) χ_i(1) χ_i(z⁻¹) = |G| · (Ĉ · D̂)(z)`,

and `(Ĉ · D̂)(z) = |{(x,y) ∈ C × D : x y = z}|`.

Both `ω_i(Ĉ) ω_i(D̂) χ_i(1) = ∑_g (Ĉ D̂)(g) χ_i(g)` (multiplicativity of the central character plus
`centralScalar_mul_character_one`) and the collapse of `∑_i χ_i(z⁻¹) χ_i(g)` by the second
orthogonality relation are already available; what remains is that the coefficients of a central
element are constant on classes, so the surviving sum is `|cl(z)| · |C_G(z)| = |G|` times the
coefficient at `z`. -/
theorem sum_centralScalar_mul_character_eq_card_mul_coeff (C D : ConjClasses G) (z : G) :
    ∑ j : ι', MatrixModule.centralScalar e.toAlgHom.toRingHom j (classSum C)
        * MatrixModule.centralScalar e.toAlgHom.toRingHom j (classSum D)
        * (wedderburnRepresentation e j).character 1
        * (wedderburnRepresentation e j).character z⁻¹
      = (Nat.card G : K) * (classSum (k := K) C * classSum (k := K) D).coeff z := by
  classical
  set w : MonoidAlgebra K G := classSum (k := K) C * classSum (k := K) D with hwdef
  have hw : w ∈ Subalgebra.center K (MonoidAlgebra K G) :=
    Subalgebra.mul_mem _ (classSum_mem_center C) (classSum_mem_center D)
  -- rewrite each summand through `ω_j(Ĉ)ω_j(D̂) χ_j(1) = ∑_g w(g) χ_j(g)`
  have hterm : ∀ j : ι',
      MatrixModule.centralScalar e.toAlgHom.toRingHom j (classSum C)
          * MatrixModule.centralScalar e.toAlgHom.toRingHom j (classSum D)
          * (wedderburnRepresentation e j).character 1
          * (wedderburnRepresentation e j).character z⁻¹
        = ∑ g : G, w.coeff g * ((wedderburnRepresentation e j).character g
            * (wedderburnRepresentation e j).character z⁻¹) := by
    intro j
    rw [← centralScalar_mul e j (classSum_mem_center C) (classSum_mem_center D),
      centralScalar_mul_character_one e j w hw, Finset.sum_mul]
    exact Finset.sum_congr rfl fun g _ => by ring
  rw [Finset.sum_congr rfl fun j _ => hterm j, Finset.sum_comm]
  -- collapse the inner sum by column orthogonality
  have hcol : ∀ g : G, ∑ j : ι', w.coeff g * ((wedderburnRepresentation e j).character g
      * (wedderburnRepresentation e j).character z⁻¹)
      = if IsConj z g then w.coeff z * (Nat.card (Subgroup.centralizer ({z} : Set G)) : K)
        else 0 := by
    intro g
    rw [← Finset.mul_sum]
    have horth : ∑ j : ι', (wedderburnRepresentation e j).character g
        * (wedderburnRepresentation e j).character z⁻¹
        = if IsConj z g then (Nat.card (Subgroup.centralizer ({z} : Set G)) : K) else 0 := by
      rw [← sum_character_inv_mul_character e z g]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    rw [horth]
    by_cases hg : IsConj z g
    · rw [if_pos hg, if_pos hg,
        coeff_center_of_mk_eq hw (ConjClasses.mk_eq_mk_iff_isConj.mpr hg.symm)]
    · rw [if_neg hg, if_neg hg, mul_zero]
  rw [Finset.sum_congr rfl fun g _ => hcol g]
  -- the surviving terms are the class of `z`, of size `|cl(z)|`
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero, nsmul_eq_mul]
  have hfil : (Finset.univ.filter (fun g : G => IsConj z g)).card
      = conjugacyClassSize (ConjClasses.mk z) := by
    rw [conjugacyClassSize, Nat.card_eq_fintype_card, ← Set.toFinset_card]
    congr 1
    ext g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_toFinset,
      ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj]
    exact ⟨fun h => h.symm, fun h => h.symm⟩
  rw [hfil]
  have hG : (conjugacyClassSize (ConjClasses.mk z) : K)
      * (Nat.card (Subgroup.centralizer ({z} : Set G)) : K) = (Nat.card G : K) := by
    rw [← Nat.cast_mul, conjugacyClassSize_mk_mul_card_centralizer]
  calc (conjugacyClassSize (ConjClasses.mk z) : K)
        * (w.coeff z * (Nat.card (Subgroup.centralizer ({z} : Set G)) : K))
      = ((conjugacyClassSize (ConjClasses.mk z) : K)
          * (Nat.card (Subgroup.centralizer ({z} : Set G)) : K)) * w.coeff z := by ring
    _ = (Nat.card G : K) * w.coeff z := by rw [hG]

end Burnside

end OddOrder.RepresentationTheory.Modular
