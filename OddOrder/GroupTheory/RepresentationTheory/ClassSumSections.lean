/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.RepresentationTheory.Subrepresentation
import Mathlib.RepresentationTheory.Character
import Mathlib.LinearAlgebra.Trace
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.Group.Conj
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.GroupTheory.GroupAction.Quotient
import OddOrder.GroupTheory.TISubset
import OddOrder.Algebra.AlgInt
import OddOrder.GroupTheory.FreeActionOrbitCount
import OddOrder.GroupTheory.ConjClassSet
import OddOrder.GroupTheory.RepresentationTheory.AbsolutelyIrreducible
import OddOrder.GroupTheory.ConjClassCardinality
import OddOrder.Mathlib.Sylow
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.LinearAlgebra.Eigenspace.Semisimple
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Polynomial.RationalRoot

/-!
# Class sums — indexing, structure coefficients, and the pair action

The `ClassSum`, `StructureCoeff`, `StructureCoeffAtIdentity` and `PairAction`
sections of the class-sum congruence development.  `mk_eq_one_iff_eq_one` is public
here because the congruence layer in the parent consumes it (no cross-file
`private`).

Split from the parent file (issue 0149, the longFile-1500 campaign); the parent
imports this leaf, so downstream imports are unchanged.
-/


namespace OddOrder.RepresentationTheory

open scoped MonoidAlgebra
open Module (finrank)
open Representation

variable {G : Type*} [Group G]

section ClassSum

variable [Fintype G] [DecidableEq (ConjClasses G)]

/-- The **class sum** of a conjugacy class `C` of `G`: the element `∑_{x ∈ C} x` of the group
algebra `ℂ[G]`.  This is Peterfalvi's `C_s` and Isaacs' `\hat C` (§3, p. 35). -/
noncomputable def classSum (C : ConjClasses G) : ℂ[G] :=
  ∑ g : G, if ConjClasses.mk g = C then MonoidAlgebra.of ℂ G g else 0

/-- The coefficient of `classSum C` at a group element `x` is `1` if `x` lies in the class `C`
and `0` otherwise. -/
theorem classSum_apply (C : ConjClasses G) (x : G) :
    classSum C x = if ConjClasses.mk x = C then 1 else 0 := by
  classical
  have hsum : classSum C x
      = ∑ g : G, (if ConjClasses.mk g = C then MonoidAlgebra.of ℂ G g else 0) x := by
    rw [classSum]; exact map_sum (Finsupp.applyAddHom x) _ Finset.univ
  -- `(0 : ℂ[G]) y = 0` (the `MonoidAlgebra` zero coefficient), used below.
  have hzero : ∀ y : G, (0 : MonoidAlgebra ℂ G) y = 0 := fun _ => rfl
  -- The coefficient of each summand at `x`: `1` if `g = x` and `mk g = C`, else `0`.
  have hterm : ∀ g : G, (if ConjClasses.mk g = C then MonoidAlgebra.of ℂ G g else 0) x
      = if g = x then (if ConjClasses.mk g = C then (1 : ℂ) else 0) else 0 := by
    intro g
    rw [apply_ite (fun f : MonoidAlgebra ℂ G => f x), MonoidAlgebra.of_apply,
      MonoidAlgebra.single_apply, hzero x]
    by_cases hg : g = x
    · rw [if_pos hg, if_pos hg]
    · rw [if_neg hg, if_neg hg, ite_self]
  rw [hsum, Finset.sum_congr rfl (fun g _ => hterm g),
    Finset.sum_ite_eq' Finset.univ x (fun g => if ConjClasses.mk g = C then (1 : ℂ) else 0)]
  simp

/-- **Class sums are central in `ℂ[G]`.** Conjugation by any group element permutes each conjugacy
class, so `classSum C` commutes with every basis element `of ℂ G h`, hence with all of `ℂ[G]`.
(Isaacs §3; Peterfalvi (6.7.2).) -/
theorem classSum_mem_center (C : ConjClasses G) :
    classSum C ∈ Subalgebra.center ℂ (ℂ[G]) := by
  classical
  rw [Subalgebra.mem_center_iff]
  intro a
  -- Reduce to basis elements `a = single h r` by linearity.
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => rw [add_mul, mul_add, hx, hy]
  | single h r =>
    -- `single h r = r • of ℂ G h`, and scalars commute, so reduce to `of ℂ G h`.
    have hof : (MonoidAlgebra.single h r : ℂ[G]) = r • MonoidAlgebra.of ℂ G h := by
      rw [MonoidAlgebra.of_apply, MonoidAlgebra.smul_single, smul_eq_mul, mul_one]
    rw [hof, smul_mul_assoc, mul_smul_comm]
    congr 1
    -- Goal: `of h * classSum C = classSum C * of h`.
    rw [classSum, Finset.mul_sum, Finset.sum_mul]
    -- LHS term: `of h * (if mk g = C then of g else 0)`; reindex `g ↦ h * g * h⁻¹`.
    rw [← Equiv.sum_comp (MulAut.conj h).toEquiv
      (fun g => (if ConjClasses.mk g = C then MonoidAlgebra.of ℂ G g else 0) *
        MonoidAlgebra.of ℂ G h)]
    refine Finset.sum_congr rfl fun g _ => ?_
    have hconj : (MulAut.conj h).toEquiv g = h * g * h⁻¹ := by simp [MulAut.conj_apply]
    rw [hconj]
    have hclass : ConjClasses.mk (h * g * h⁻¹) = ConjClasses.mk g :=
      ConjClasses.mk_eq_mk_iff_isConj.mpr (isConj_iff.mpr ⟨h⁻¹, by group⟩)
    rw [hclass]
    by_cases h0 : ConjClasses.mk g = C
    · simp only [h0, if_true]
      rw [← map_mul, ← map_mul]
      congr 1
      group
    · simp [h0]

end ClassSum

section StructureCoeff

variable [Fintype G] [DecidableEq G] [DecidableEq (ConjClasses G)]

/-- The **structure coefficient** `a_{ijs}`: the number of ordered pairs `(u, v)` with `u ∈ C_i`,
`v ∈ C_j`, and `u·v ∈ C_s`.  These are the natural numbers in Peterfalvi's `C_i · C_j = ∑_s a_{ijs}
· C_s` (note that the coefficient of the *class sum* `C_s` in that combination is `a_{ijs}/|C_s|`;
the unscaled `a_{ijs}` counts pairs over the whole class). -/
noncomputable def classSumCoeff (Ci Cj Cs : ConjClasses G) : ℕ :=
  (Finset.univ.filter (fun p : G × G =>
    ConjClasses.mk p.1 = Ci ∧ ConjClasses.mk p.2 = Cj ∧ ConjClasses.mk (p.1 * p.2) = Cs)).card

/-- **Coefficient of a product of class sums at a group element.** The coefficient of `w` in
`classSum Ci * classSum Cj` is the number of factorizations `w = u·v` with `u ∈ C_i` and `v ∈ C_j`.
(This per-element count is constant on each conjugacy class; summing it over a class `C_s` recovers
the structure coefficient `classSumCoeff Ci Cj Cs`.) -/
theorem classSum_mul_apply (Ci Cj : ConjClasses G) (w : G) :
    (classSum Ci * classSum Cj) w =
      (Finset.univ.filter (fun p : G × G =>
        ConjClasses.mk p.1 = Ci ∧ ConjClasses.mk p.2 = Cj ∧ p.1 * p.2 = w)).card := by
  classical
  -- Expand the product coefficient over all pairs `(u, v)` with `u * v = w`.
  have hexp := MonoidAlgebra.mul_apply_antidiagonal (classSum Ci) (classSum Cj) w
    (Finset.univ.filter (fun p : G × G => p.1 * p.2 = w)) (by intro p; simp)
  rw [hexp]
  -- Each summand is the product of two `0/1` indicators; combine into a single indicator.
  have hbody : ∀ p : G × G,
      (classSum Ci p.1) * (classSum Cj p.2)
        = if ConjClasses.mk p.1 = Ci ∧ ConjClasses.mk p.2 = Cj then (1 : ℂ) else 0 := by
    intro p
    rw [classSum_apply, classSum_apply, ite_and]
    by_cases h1 : ConjClasses.mk p.1 = Ci <;> by_cases h2 : ConjClasses.mk p.2 = Cj <;>
      simp [h1, h2]
  rw [Finset.sum_congr rfl (fun p _ => hbody p)]
  -- Sum of a `0/1` indicator over the antidiagonal is the cardinality of the counted set.
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
  norm_cast
  apply congrArg Finset.card
  ext p
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hw, hi, hj⟩; exact ⟨hi, hj, hw⟩
  · rintro ⟨hi, hj, hw⟩; exact ⟨hw, hi, hj⟩

omit [Fintype G] [DecidableEq G] [DecidableEq (ConjClasses G)] in
/-- The conjugacy class of `h * g * h⁻¹` is the same as that of `g`. -/
private theorem mk_conj_eq (h g : G) : ConjClasses.mk (h * g * h⁻¹) = ConjClasses.mk g :=
  ConjClasses.mk_eq_mk_iff_isConj.mpr (isConj_iff.mpr ⟨h⁻¹, by group⟩)

omit [DecidableEq G] in
/-- The per-element product coefficient `(classSum Ci * classSum Cj) w` is a **class function** of
`w`: conjugating `w` by any group element leaves the number of factorizations unchanged.  (The
bijection `(u, v) ↦ (h u h⁻¹, h v h⁻¹)` preserves the class of each factor and maps `u·v = w` to
`(h u h⁻¹)·(h v h⁻¹) = h w h⁻¹`.) -/
theorem classSum_mul_apply_conj (Ci Cj : ConjClasses G) (h w : G) :
    (classSum Ci * classSum Cj) (h * w * h⁻¹) = (classSum Ci * classSum Cj) w := by
  classical
  rw [classSum_mul_apply, classSum_mul_apply]
  norm_cast
  -- `i` sends a factorization of `h·w·h⁻¹` to one of `w` by conjugating *down* by `h`.
  refine Finset.card_nbij' (fun p => (h⁻¹ * p.1 * h, h⁻¹ * p.2 * h))
    (fun p => (h * p.1 * h⁻¹, h * p.2 * h⁻¹)) ?_ ?_ ?_ ?_
  · rintro ⟨u, v⟩ hp
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hp ⊢
    obtain ⟨hi, hj, huv⟩ := hp
    refine ⟨?_, ?_, ?_⟩
    · rw [show h⁻¹ * u * h = h⁻¹ * u * h⁻¹⁻¹ by group, mk_conj_eq, hi]
    · rw [show h⁻¹ * v * h = h⁻¹ * v * h⁻¹⁻¹ by group, mk_conj_eq, hj]
    · rw [show h⁻¹ * u * h * (h⁻¹ * v * h) = h⁻¹ * (u * v) * h by group, huv]; group
  · rintro ⟨u, v⟩ hp
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hp ⊢
    obtain ⟨hi, hj, huv⟩ := hp
    refine ⟨?_, ?_, ?_⟩
    · rw [mk_conj_eq, hi]
    · rw [mk_conj_eq, hj]
    · rw [show h * u * h⁻¹ * (h * v * h⁻¹) = h * (u * v) * h⁻¹ by group, huv]
  · rintro ⟨u, v⟩ _; simp only [Prod.mk.injEq]; constructor <;> group
  · rintro ⟨u, v⟩ _; simp only [Prod.mk.injEq]; constructor <;> group

omit [DecidableEq G] in
/-- The per-element product coefficient equals the count taken at the chosen class representative
`(ConjClasses.mk w).out`. -/
theorem classSum_mul_apply_out (Ci Cj : ConjClasses G) (w : G) :
    (classSum Ci * classSum Cj) w = (classSum Ci * classSum Cj) (ConjClasses.mk w).out := by
  classical
  -- `(mk w).out` is conjugate to `w`, so write it as `h * w * h⁻¹` and apply class-invariance.
  have hmk : ConjClasses.mk (ConjClasses.mk w).out = ConjClasses.mk w := by
    rw [← ConjClasses.quotient_mk_eq_mk, Quotient.out_eq]
  have hconj : IsConj w (ConjClasses.mk w).out :=
    ConjClasses.mk_eq_mk_iff_isConj.mp hmk.symm
  obtain ⟨c, hc⟩ := isConj_iff.mp hconj
  rw [← hc, classSum_mul_apply_conj]

variable [Fintype (ConjClasses G)]

omit [DecidableEq G] in
/-- **Product of class sums as an integer combination of class sums** (Isaacs §3; Peterfalvi
(6.7.2)): `C_i · C_j = ∑_s a_{ijs}^∘ · C_s`, where the coefficient of `C_s` is the per-element
factorization count `(classSum Ci * classSum Cj) (out C_s)` — a natural number that is *constant*
on the class (this is the coefficient that is actually consistent with `classSum_mul_apply`, **not**
the pair-count `classSumCoeff` divided by `|C_s|`). -/
theorem classSum_mul (Ci Cj : ConjClasses G) :
    classSum Ci * classSum Cj =
      ∑ Cs : ConjClasses G, ((classSum Ci * classSum Cj) Cs.out : ℂ) • classSum Cs := by
  classical
  -- Compare coefficients at an arbitrary group element `w`.
  apply MonoidAlgebra.ext
  intro w
  -- Push the coefficient evaluation `· w` through the finite sum (as an additive hom).
  have hrhs : (∑ Cs : ConjClasses G,
        ((classSum Ci * classSum Cj) Cs.out : ℂ) • classSum Cs) w
      = ∑ Cs : ConjClasses G, (((classSum Ci * classSum Cj) Cs.out : ℂ) • classSum Cs) w :=
    map_sum (Finsupp.applyAddHom w) _ Finset.univ
  rw [hrhs]
  -- RHS coefficient at `w`: only the `Cs = mk w` term survives, contributing `κ((mk w).out)`.
  have hterm : ∀ Cs : ConjClasses G,
      (((classSum Ci * classSum Cj) Cs.out : ℂ) • classSum Cs) w
        = if Cs = ConjClasses.mk w then (classSum Ci * classSum Cj) Cs.out else 0 := by
    intro Cs
    rw [MonoidAlgebra.smul_apply, classSum_apply, smul_eq_mul]
    by_cases hCs : ConjClasses.mk w = Cs
    · rw [if_pos hCs, if_pos hCs.symm, mul_one]
    · rw [if_neg hCs, if_neg (fun h => hCs h.symm), mul_zero]
  rw [Finset.sum_congr rfl (fun Cs _ => hterm Cs),
    Finset.sum_ite_eq' Finset.univ (ConjClasses.mk w)
      (fun Cs => (classSum Ci * classSum Cj) Cs.out)]
  rw [if_pos (Finset.mem_univ _)]
  exact classSum_mul_apply_out Ci Cj w

end StructureCoeff

section StructureCoeffAtIdentity

/-- `mk w = 1` (the identity conjugacy class) iff `w = 1`. -/
theorem mk_eq_one_iff_eq_one {w : G} : ConjClasses.mk w = 1 ↔ w = 1 := by
  rw [ConjClasses.one_eq_mk_one, ConjClasses.mk_eq_mk_iff_isConj, isConj_one_left]

variable [Fintype G] [DecidableEq (ConjClasses G)]

/-- **Peterfalvi (6.7.3), structure constant `a_{ij0} = 0`.** The coefficient of the *identity*
class in `classSumCoeff Ci Cj 1` counts ordered pairs `(u, v)` with `u ∈ C_i`, `v ∈ C_j` and
`u·v = 1`, i.e. `v = u⁻¹` with `mk u = C_i` and `mk u⁻¹ = C_j`.  If no element of `C_i` has its
inverse in `C_j` (`∀ u, mk u = C_i → mk u⁻¹ ≠ C_j`), the count is `0`.

This is Peterfalvi's `a_{110} = 0`: with `C_i = C_j = C₁ = ⟦z⟧` and `⟦z⁻¹⟧ ≠ ⟦z⟧` (no nontrivial
real class in odd order), an element `u ∈ C₁` has `u⁻¹ ∈ ⟦z⁻¹⟧ ≠ C₁`, so no pair multiplies to
`1`. -/
theorem classSumCoeff_one_eq_zero (Ci Cj : ConjClasses G)
    (h : ∀ u : G, ConjClasses.mk u = Ci → ConjClasses.mk u⁻¹ ≠ Cj) :
    classSumCoeff Ci Cj 1 = 0 := by
  rw [classSumCoeff, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro ⟨u, v⟩ -
  rintro ⟨hi, hj, huv⟩
  -- `mk (u·v) = 1` forces `u·v = 1`, i.e. `u⁻¹ = v`; then `mk u⁻¹ = mk v = C_j` contradicts `h`.
  rw [mk_eq_one_iff_eq_one] at huv
  exact (h u hi) (by rw [inv_eq_of_mul_eq_one_right huv]; exact hj)

/-- **Peterfalvi (6.7.3), structure constant `a_{ij0} = |C_i|`.** When `C_j` is the *inverse* class
of `C_i` (every `u ∈ C_i` has `u⁻¹ ∈ C_j`), the coefficient of the identity class
`classSumCoeff Ci Cj 1` equals `|C_i|`: the pairs with product `1` are exactly `(u, u⁻¹)` for
`u ∈ C_i`, a bijection with `C_i`.

This is Peterfalvi's `a_{120} = |C₁|`: with `C_i = C₁ = ⟦z⟧` and `C_j = C₂ = ⟦z⁻¹⟧`, each `u ∈ C₁`
contributes the single pair `(u, u⁻¹)`.  The hypothesis `hinv` (that `mk u⁻¹ = C_j` for all
`u ∈ C_i`) holds for `C_j = ⟦z⁻¹⟧` because `mk u = ⟦z⟧ ⟹ mk u⁻¹ = ⟦z⁻¹⟧`. -/
theorem classSumCoeff_one_eq_card (Ci Cj : ConjClasses G)
    (hinv : ∀ u : G, ConjClasses.mk u = Ci → ConjClasses.mk u⁻¹ = Cj) :
    classSumCoeff Ci Cj 1 = Nat.card { x : G // ConjClasses.mk x = Ci } := by
  classical
  rw [classSumCoeff, Nat.card_eq_fintype_card,
    Fintype.card_subtype (p := fun x => ConjClasses.mk x = Ci)]
  -- The pair set `{(u,v) : mk u = Ci, mk v = Cj, mk (u·v) = 1}` is in bijection with
  -- `{u : mk u = Ci}` via `u ↦ (u, u⁻¹)`, inverse `(u,v) ↦ u`.
  refine Finset.card_nbij' (fun p => p.1) (fun u => (u, u⁻¹)) ?_ ?_ ?_ ?_
  · rintro ⟨u, v⟩ hp
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hp ⊢
    exact hp.1
  · intro u hu
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hu ⊢
    refine ⟨hu, hinv u hu, ?_⟩
    rw [mul_inv_cancel, mk_eq_one_iff_eq_one]
  · rintro ⟨u, v⟩ hp
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hp
    obtain ⟨-, -, hs⟩ := hp
    -- `mk (u·v) = 1` ⟹ `u·v = 1` ⟹ `v = u⁻¹`, so `(u, u⁻¹) = (u, v)`.
    rw [mk_eq_one_iff_eq_one] at hs
    simp [inv_eq_of_mul_eq_one_right hs]
  · intro u _; rfl

/-- **Peterfalvi (6.7.3), `a_{110} = 0` keyed to `z`.** With `C_1 = ⟦z⟧`, the coefficient of the
identity class in `C_1 · C_1` is `0` provided `z⁻¹` is not `G`-conjugate to `z`
(`⟦z⁻¹⟧ ≠ ⟦z⟧`).  This is the direct instance of `classSumCoeff_one_eq_zero` consumed by (6.7.3):
the only hypothesis is the real-class atom `⟦z⁻¹⟧ ≠ ⟦z⟧` (from `|L|` odd). -/
theorem classSumCoeff_self_one_eq_zero (z : G)
    (hz : ConjClasses.mk z⁻¹ ≠ ConjClasses.mk z) :
    classSumCoeff (ConjClasses.mk z) (ConjClasses.mk z) 1 = 0 := by
  refine classSumCoeff_one_eq_zero _ _ fun u hu => ?_
  -- `mk u = ⟦z⟧ ⟹ mk u⁻¹ = ⟦z⁻¹⟧ ≠ ⟦z⟧`.
  rw [mk_inv_eq_of_mk_eq hu]
  exact hz

/-- **Peterfalvi (6.7.3), `a_{120} = |C_1|` keyed to `z`.** With `C_1 = ⟦z⟧` and `C_2 = ⟦z⁻¹⟧`
(the inverse class), the coefficient of the identity class in `C_1 · C_2` is `|C_1|`.  This is the
direct instance of `classSumCoeff_one_eq_card` consumed by (6.7.3); the inverse-class hypothesis
`∀ u, mk u = ⟦z⟧ → mk u⁻¹ = ⟦z⁻¹⟧` is *unconditional* (`mk_inv_eq_of_mk_eq`). -/
theorem classSumCoeff_self_inv_one_eq_card (z : G) :
    classSumCoeff (ConjClasses.mk z) (ConjClasses.mk z⁻¹) 1
      = Nat.card { x : G // ConjClasses.mk x = ConjClasses.mk z } :=
  classSumCoeff_one_eq_card _ _ fun _ hu => mk_inv_eq_of_mk_eq hu

end StructureCoeffAtIdentity

section PairAction

variable [Fintype G] [DecidableEq G] [DecidableEq (ConjClasses G)]

/-- The defining predicate of the pair set `Ω = {(u,v) ∈ C_i × C_j ∣ u·v ∈ C_s}` of Peterfalvi
(6.7.1): an ordered pair `q = (u, v)` with `u ∈ C_i`, `v ∈ C_j` and `u·v ∈ C_s`. -/
def IsClassPair (Ci Cj Cs : ConjClasses G) (q : G × G) : Prop :=
  ConjClasses.mk q.1 = Ci ∧ ConjClasses.mk q.2 = Cj ∧ ConjClasses.mk (q.1 * q.2) = Cs

omit [Fintype G] [DecidableEq G] [DecidableEq (ConjClasses G)] in
/-- Conjugation preserves the pair predicate: if `q` lies in `Ω` then so does `(x q.1 x⁻¹, x q.2
x⁻¹)`, because conjugation fixes every conjugacy class and is multiplicative. -/
theorem isClassPair_conj {Ci Cj Cs : ConjClasses G} {q : G × G}
    (hq : IsClassPair Ci Cj Cs q) (x : G) :
    IsClassPair Ci Cj Cs (x * q.1 * x⁻¹, x * q.2 * x⁻¹) := by
  obtain ⟨h1, h2, h3⟩ := hq
  refine ⟨by rw [mk_conj_eq, h1], by rw [mk_conj_eq, h2], ?_⟩
  rw [show x * q.1 * x⁻¹ * (x * q.2 * x⁻¹) = x * (q.1 * q.2) * x⁻¹ by group, mk_conj_eq, h3]

/-- The pair set `Ω` of Peterfalvi (6.7.1), as a subtype of `G × G`. -/
abbrev ClassPair (Ci Cj Cs : ConjClasses G) : Type _ := { q : G × G // IsClassPair Ci Cj Cs q }

/-- The **conjugation action of a subgroup `P ≤ G` on the pair set `Ω`** of Peterfalvi (6.7.1):
`x • (u, v) = (x u x⁻¹, x v x⁻¹)`.  This is the action whose fixed-point-freeness (no `x ∈ P^#`
fixes a pair) yields `|P| ∣ a_{ijs}|C_s| = |Ω|`. -/
instance classPairSMul (P : Subgroup G) (Ci Cj Cs : ConjClasses G) :
    SMul P (ClassPair Ci Cj Cs) where
  smul x q := ⟨((x : G) * q.1.1 * (x : G)⁻¹, (x : G) * q.1.2 * (x : G)⁻¹),
    isClassPair_conj q.2 (x : G)⟩

omit [Fintype G] [DecidableEq G] [DecidableEq (ConjClasses G)] in
@[simp] theorem classPairSMul_coe (P : Subgroup G) {Ci Cj Cs : ConjClasses G} (x : P)
    (q : ClassPair Ci Cj Cs) :
    ((x • q : ClassPair Ci Cj Cs) : G × G) = ((x : G) * q.1.1 * (x : G)⁻¹,
      (x : G) * q.1.2 * (x : G)⁻¹) := rfl

instance classPairMulAction (P : Subgroup G) (Ci Cj Cs : ConjClasses G) :
    MulAction P (ClassPair Ci Cj Cs) where
  one_smul q := by
    apply Subtype.ext
    rw [classPairSMul_coe]
    simp
  mul_smul x y q := by
    apply Subtype.ext
    rw [classPairSMul_coe, classPairSMul_coe, classPairSMul_coe]
    simp only [Subgroup.coe_mul, Prod.mk.injEq]
    constructor <;> group

omit [DecidableEq G] in
/-- The cardinality of the pair set `Ω` equals the structure coefficient `a_{ijs}|C_s| =
`classSumCoeff Ci Cj Cs` (Peterfalvi's `a_{ijs}|{\cal C}_s|`). -/
theorem card_classPair (Ci Cj Cs : ConjClasses G) :
    Nat.card (ClassPair Ci Cj Cs) = classSumCoeff Ci Cj Cs := by
  classical
  rw [classSumCoeff, Nat.card_eq_fintype_card,
    Fintype.card_subtype (p := fun q => IsClassPair Ci Cj Cs q)]
  congr 1
  ext q
  simp only [Finset.mem_filter, IsClassPair]

omit [DecidableEq G] in
/-- **Peterfalvi (6.7.1)** (orbit-counting half).  Let `P ≤ G` be a finite subgroup acting on the
pair set `Ω = {(u,v) ∈ C_i × C_j ∣ u·v ∈ C_s}` by conjugation.  If `P` acts *fixed-point-freely* —
no `x ∈ P` with `x ≠ 1` fixes a pair of `Ω` — then `|P| ∣ a_{ijs}|C_s|`, i.e. `|P|` divides the
structure-coefficient count `classSumCoeff Ci Cj Cs`.

This packages the counting step of (6.7.1): the remaining content of (6.7.1) is precisely the
group-theoretic verification of the fixed-point-free hypothesis (`P^#` TI-subset ⟹ `C_G(x) ⊆ L`,
a `p`-element of `L` lies in `P`, conjugacy into `Z^#` with `Z ⊴ L` forces it into `Z`,
contradicting `C_s ∩ Z = ∅`). -/
theorem card_dvd_classSumCoeff_of_fixedPointFree (P : Subgroup G) [Finite P]
    (Ci Cj Cs : ConjClasses G)
    (hfree : ∀ x : P, (x : G) ≠ 1 → ∀ q : ClassPair Ci Cj Cs, x • q ≠ q) :
    Nat.card P ∣ classSumCoeff Ci Cj Cs := by
  rw [← card_classPair]
  refine card_dvd_of_no_nontrivial_fixed (Γ := P) (β := ClassPair Ci Cj Cs) ?_
  intro x hx q
  exact hfree x (by simpa using hx) q

end PairAction


end OddOrder.RepresentationTheory
