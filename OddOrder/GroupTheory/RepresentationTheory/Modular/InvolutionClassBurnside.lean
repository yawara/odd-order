/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.Modular.BlockPartVanishing
import OddOrder.GroupTheory.RepresentationTheory.Modular.CentralCharacterTrace
import OddOrder.GroupTheory.RepresentationTheory.Modular.OrdinaryBasis
import OddOrder.GroupTheory.UniqueInvolutionSylow

/-!
# Navarro p. 144: the Burnside step at the class of an involution

Navarro's Brauer–Suzuki argument reaches the point where it needs

`∑_{χ ∈ Irr(G)} χ(t)²/χ(1) · χ(s) = 0`  for every `2`-singular `s`,

`t` an involution.  The input is purely group-theoretic — **the product of two involutions has odd
order** (`odd_orderOf_mul_of_involution_of_unique_involution`), so the class `K = cl(t)` satisfies
`K · K ∩ {2\text{-singular}} = ∅` — and the bridge is Burnside's class-multiplication formula.

Everything here is kept **division-free**: instead of `χ(t)²/χ(1)` the class function carries the
coefficients

`c_i = ω_i(K̂)² χ_i(1)`  ( `= |K|² χ_i(t)²/χ_i(1)` , since `ω_i(K̂) χ_i(1) = |K| χ_i(t)` ),

for which Burnside reads `∑_i c_i χ_i(g) = |G| · (K̂ · K̂)(g⁻¹)` with no denominators at all.  This
also removes the need for the ordinary character table over `ℂ`: the whole step runs in the
splitting field `K` of the `p`-modular system, which is what the modular chain downstream uses.

Composing with the first half of Navarro (5.10)
(`sum_ordinaryCoeff_mul_generalizedDecompositionNumber_eq_zero`) turns the vanishing into the
orthogonality `(Θ, D^x_μ) = 0` against every generalized decomposition column, which is the form
the basic-set columns of the "analysis at `t`" consume.

## Main results

* `OddOrder.RepresentationTheory.Modular.classSquareFn_eq_card_mul_coeff` — Burnside, packaged as
  a class function with an `Irr(G)`-expansion
* `OddOrder.RepresentationTheory.Modular.coeff_classSum_mul_self_eq_zero_of_not_isPRegular` — the
  group-theoretic input: an involution class squared misses the `2`-singular elements
* `OddOrder.RepresentationTheory.Modular.classSquareFn_eq_zero_of_not_isPRegular`
* `OddOrder.RepresentationTheory.Modular`
  `.sum_classSquareCoeff_mul_generalizedDecompositionNumber_eq_zero` — Navarro (8)/(9) on p. 144
-/

namespace OddOrder.RepresentationTheory.Modular

open IsLocalRing Matrix MonoidAlgebra OddOrder.GroupTheory OddOrder.GroupTheory.CenterClassSum

/-! ### The group-theoretic input: `cl(t) · cl(t)` misses the `2`-singular elements -/

section ClassProduct

variable {k G : Type*} [CommSemiring k] [Group G] [Fintype G] [DecidableEq (ConjClasses G)]

omit [Fintype G] [DecidableEq (ConjClasses G)] in
/-- Conjugate elements have the same order. -/
theorem orderOf_eq_of_isConj {a b : G} (h : IsConj a b) : orderOf a = orderOf b := by
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  rw [← hc, orderOf_conj]

/-- **The square of an involution class misses every `2`-singular element.**

If `g = v u` with `v, u ∈ cl(t)` then `v` and `u` are involutions, so `g` has odd order
(`odd_orderOf_mul_of_involution_of_unique_involution`) and is therefore `2`-regular.  Hence for
`2`-singular `g` every term of `(K̂ · K̂)(g) = ∑_{v ∈ K} K̂(v⁻¹ g)` vanishes.

This is the step on Navarro p. 143–144 that turns "a Sylow `2`-subgroup has a unique involution"
into the character identity (8). -/
theorem coeff_classSum_mul_self_eq_zero_of_not_isPRegular (T : Sylow 2 G) {z : G}
    (hz : ∀ s ∈ (T : Subgroup G), s ^ 2 = 1 → s = 1 ∨ s = z) {t : G} (ht : orderOf t = 2) {g : G}
    (hg : ¬ IsPRegular 2 g) :
    (classSum (k := k) (ConjClasses.mk t) * classSum (k := k) (ConjClasses.mk t)).coeff g = 0 := by
  classical
  rw [coeff_classSum_mul]
  refine Finset.sum_eq_zero fun v hv => ?_
  rw [coeff_classSum, if_neg]
  intro hmk
  -- both factors of `g = v * (v⁻¹ * g)` are conjugates of `t`, hence involutions
  have hvord : orderOf v = 2 :=
    (orderOf_eq_of_isConj (ConjClasses.mk_eq_mk_iff_isConj.mp
      (Finset.mem_filter.mp hv).2)).trans ht
  have huord : orderOf (v⁻¹ * g) = 2 :=
    (orderOf_eq_of_isConj (ConjClasses.mk_eq_mk_iff_isConj.mp hmk)).trans ht
  have hodd : Odd (orderOf (v * (v⁻¹ * g))) :=
    odd_orderOf_mul_of_involution_of_unique_involution T hz hvord huord
  rw [show v * (v⁻¹ * g) = g by group] at hodd
  exact hg (Nat.not_even_iff_odd.mpr hodd ∘ (even_iff_two_dvd (α := ℕ)).mpr)

end ClassProduct

/-! ### Burnside, packaged as a class function -/

section Burnside

variable {K G : Type*} [Field K] [Group G] [Fintype G] [DecidableEq (ConjClasses G)]
variable {ι' : Type*} {m : ι' → Type*} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
  [∀ i, Nonempty (m i)] [Fintype ι'] [Invertible (Nat.card G : K)]
variable (e : MonoidAlgebra K G ≃ₐ[K] ∀ i, Matrix (m i) (m i) K)

/-- The **division-free form of Navarro's `χ(t)²/χ(1)`**: the coefficient
`c_i = ω_i(Ĉ)² χ_i(1)`.  Since `ω_i(Ĉ) χ_i(1) = |C| χ_i(x_C)`, this is `|C|² χ_i(x_C)²/χ_i(1)`. -/
noncomputable def classSquareCoeff (C : ConjClasses G) (i : ι') : K :=
  MatrixModule.centralScalar e.toAlgHom.toRingHom i (classSum C) ^ 2
    * (wedderburnRepresentation e i).character 1

/-- The class function `∑_i c_i χ_i` attached to a class `C` by `classSquareCoeff`. -/
noncomputable def classSquareFn (C : ConjClasses G) : G → K :=
  fun g => ∑ i : ι', classSquareCoeff e C i * (wedderburnRepresentation e i).character g

set_option maxHeartbeats 400000 in
-- Burnside is applied at `g⁻¹`, under the same instance chain that carries `e`.
/-- **Burnside's class-multiplication formula, read as a class function.**

`∑_i ω_i(Ĉ)² χ_i(1) χ_i(g) = |G| · (Ĉ · Ĉ)(g⁻¹)`.

This is `sum_centralScalar_mul_character_eq_card_mul_coeff` at `z = g⁻¹`, with the two class sums
equal. -/
theorem classSquareFn_eq_card_mul_coeff (C : ConjClasses G) (g : G) :
    classSquareFn e C g
      = (Nat.card G : K) * (classSum (k := K) C * classSum (k := K) C).coeff g⁻¹ := by
  classical
  rw [← sum_centralScalar_mul_character_eq_card_mul_coeff e C C g⁻¹, classSquareFn]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [classSquareCoeff, inv_inv, sq, mul_assoc]

omit [Invertible (Nat.card G : K)] in
/-- `classSquareFn` is a class function, in the `∀ g h, IsConj g h → …` shape that
`ordinaryCoeff` consumes. -/
theorem classSquareFn_isConj (C : ConjClasses G) :
    ∀ g h : G, IsConj g h → classSquareFn e C g = classSquareFn e C h :=
  fun _ _ hgh => Finset.sum_congr rfl fun i _ =>
    congrArg (classSquareCoeff e C i * ·)
      (character_eq_of_isConj (wedderburnRepresentation e i) hgh)

set_option linter.unusedFintypeInType false in
/-- The coefficients of `classSquareFn` in `Irr(G)` are, by construction, `classSquareCoeff`. -/
theorem ordinaryCoeff_classSquareFn [Fintype (ConjClasses G)] (C : ConjClasses G) :
    ordinaryCoeff e (classSquareFn e C) (classSquareFn_isConj e C) = classSquareCoeff e C :=
  (eq_ordinaryCoeff e _ _ fun _ => rfl).symm

/-- **Navarro (8) on p. 144**: the class function `∑_i ω_i(K̂)² χ_i(1) χ_i` attached to the class
of an involution vanishes at every `2`-singular element. -/
theorem classSquareFn_eq_zero_of_not_isPRegular (T : Sylow 2 G) {z : G}
    (hz : ∀ s ∈ (T : Subgroup G), s ^ 2 = 1 → s = 1 ∨ s = z) {t : G} (ht : orderOf t = 2) {g : G}
    (hg : ¬ IsPRegular 2 g) :
    classSquareFn e (ConjClasses.mk t) g = 0 := by
  rw [classSquareFn_eq_card_mul_coeff,
    coeff_classSum_mul_self_eq_zero_of_not_isPRegular T hz ht
      (g := g⁻¹) (fun hreg => hg (by simpa using hreg.inv)),
    mul_zero]

end Burnside

/-! ### Every element of a nontrivial `p`-section is `p`-singular -/

section Section

variable {p : ℕ} {G : Type*} [Group G]

/-- If `x ≠ 1` then no element of the `p`-section `S(x)` is `p`-regular: its `p`-part is conjugate
to `x`, hence nontrivial. -/
theorem not_isPRegular_of_mem_pSection (hp : p.Prime) {x : G} (hx : x ≠ 1) {u : G}
    (hu : u ∈ pSection p x) : ¬ IsPRegular p u := fun hreg => by
  rw [mem_pSection_iff_isConj_pPart, pPart_eq_one_of_isPRegular hp hreg] at hu
  exact hx (isConj_one_right.mp hu)

end Section

/-! ### The orthogonality (9) against the generalized decomposition columns -/

section Orthogonality

variable {𝒪 K : Type*} [CommRing 𝒪] [IsDomain 𝒪] [ValuationRing 𝒪] [HenselianLocalRing 𝒪]
  [IsPModularSystem 2 𝒪] [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K]
variable {G : Type*} [Group G] [Fintype G] [DecidableEq (ConjClasses G)]
  [Fintype (ConjClasses G)] [Invertible (Nat.card G : K)]
-- `Irr(G)`, through the Wedderburn splitting of `KG`
variable {ι' : Type*} {m : ι' → Type*} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
  [∀ i, Nonempty (m i)] [Fintype ι']
-- `IBr(C_G(x))`
variable {ι : Type*} {nn : ι → Type*} [∀ i, Fintype (nn i)] [∀ i, DecidableEq (nn i)]
  [Fintype ι] [∀ i, Nonempty (nn i)]

set_option linter.unusedFintypeInType false in
open scoped Classical in
/-- **Navarro (9) on p. 144.**  Let `t` be an involution of a group whose Sylow `2`-subgroups have
a unique involution, and let `x ≠ 1` be a `2`-element.  Then the coefficient family
`c_χ = ω_χ(cl(t)^)² χ(1)` — Navarro's `χ(t)²/χ(1)` up to the constant `|cl(t)|²` — is orthogonal to
**every** generalized decomposition column at `x`:

`∑_{χ ∈ Irr(G)} c_χ d^x_{χμ} = 0`  for every `μ ∈ IBr(C_G(x))`.

Burnside (`classSquareFn_eq_zero_of_not_isPRegular`) says the class function `∑_χ c_χ χ` vanishes
on the whole `2`-section of `x`; the first half of Navarro (5.10)
(`sum_ordinaryCoeff_mul_generalizedDecompositionNumber_eq_zero`) converts that into the vanishing
of every coefficient.

Navarro instead solves a `3 × 3` linear system to express one basic-set column as a combination of
`2`-singular columns; going through `IBr`-independence gives all the columns at once, and the
basic-set version follows by `sum_mul_basicDecompositionNumber_left_eq_zero`. -/
theorem sum_classSquareCoeff_mul_generalizedDecompositionNumber_eq_zero
    (e : MonoidAlgebra K G ≃ₐ[K] ∀ i, Matrix (m i) (m i) K) {x : G} [Fintype ↥(centralizerOf x)]
    {π : MonoidAlgebra (ResidueField 𝒪) ↥(centralizerOf x) →+*
      ∀ j, Matrix (nn j) (nn j) (ResidueField 𝒪)}
    (hπ : Function.Surjective π)
    (hlin : ∀ (c : ResidueField 𝒪) (a : MonoidAlgebra (ResidueField 𝒪) ↥(centralizerOf x)),
      π (c • a) = c • π a)
    (hkerJ : RingHom.ker π = Ring.jacobson (MonoidAlgebra (ResidueField 𝒪) ↥(centralizerOf x)))
    {ω' : ResidueField 𝒪} (hω' : IsPrimitiveRoot ω' (pRegularExponent 2 ↥(centralizerOf x)))
    (T : Sylow 2 G) {z : G} (hz : ∀ s ∈ (T : Subgroup G), s ^ 2 = 1 → s = 1 ∨ s = z) {t : G}
    (ht : orderOf t = 2) (hx : IsPElement 2 x) (hx1 : x ≠ 1) (j : ι) :
    ∑ i, classSquareCoeff e (ConjClasses.mk t) i *
        generalizedDecompositionNumber (𝒪 := 𝒪) (nn := nn) x Nat.prime_two hω'
          hπ hlin hkerJ (wedderburnRepresentation e i).character
          (fun _ _ hgh => character_eq_of_isConj (wedderburnRepresentation e i) hgh) j = 0 := by
  rw [← ordinaryCoeff_classSquareFn e (ConjClasses.mk t)]
  exact sum_ordinaryCoeff_mul_generalizedDecompositionNumber_eq_zero Nat.prime_two e hπ hlin hkerJ
    hω' (classSquareFn e (ConjClasses.mk t)) (classSquareFn_isConj e _)
    (fun _ hu => classSquareFn_eq_zero_of_not_isPRegular e T hz ht
      (not_isPRegular_of_mem_pSection Nat.prime_two hx1 hu)) hx j

end Orthogonality

end OddOrder.RepresentationTheory.Modular
