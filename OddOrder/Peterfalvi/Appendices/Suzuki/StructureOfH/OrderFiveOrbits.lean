/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.StructureOfH.TConjugateTriple
import OddOrder.Peterfalvi.Appendices.Suzuki.StructureOfH.SquareRootFibres
import OddOrder.GroupTheory.FreeActionOrbitCount

/-!
# The `K`-orbits of `S#` in the case `orderOf (st) = 5`

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Part II, Ch. III §2, p. 118:

> It is thus sufficient to show that `s`, `r`, `r⁻¹` and the elements `r r^{-k}`
> for `k ∈ K#` form a system of representatives for the `K`-orbits of `S#`, or,
> since `|S#|/|K| = q + 1 = |K#| + 3`, that these elements are pairwise
> non-conjugate under the action of `K`.

This file sets up that counting: the index type `Fin 3 ⊕ K#`, the family
`orbitRepVal` it names, and the cardinality identity
`|ι| · |K| + 1 = |Q|` which case (b) supplies through `|Q| = |Q₀|²` and
`|K| = |Q₀| − 1`.

## Main results

* `Hypothesis.orbitRepVal` — the book's family of representatives.
* `Hypothesis.card_orbitReprIndex_mul_card_K_succ` — the counting identity.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki

namespace Hypothesis

variable {G Ω : Type*} [Group G] [MulAction G Ω] [Finite G]
  (hyp : Hypothesis G Ω)

/-- The index type of the book's system of representatives: three special
elements `s`, `r`, `r⁻¹`, and one for each `1 ≠ k ∈ K`. -/
abbrev OrbitReprIndex : Type _ := Fin 3 ⊕ {k : ↥hyp.K // k ≠ 1}

/-- The book's family of representatives, as elements of `G`. -/
noncomputable def orbitRepVal : hyp.OrbitReprIndex → G
  | Sum.inl i =>
      ![hyp.distinguishedInvolution, hyp.structureConjugator,
        hyp.structureConjugator⁻¹] i
  | Sum.inr k =>
      hyp.structureConjugator *
        ((k : G)⁻¹ * hyp.structureConjugator⁻¹ * (k : G))

lemma orbitRepVal_mem_Q (i : hyp.OrbitReprIndex) : hyp.orbitRepVal i ∈ hyp.Q := by
  cases i with
  | inl i =>
    fin_cases i
    · exact hyp.distinguishedInvolution_mem_Q
    · exact hyp.structureConjugator_mem_Q
    · exact hyp.Q.inv_mem hyp.structureConjugator_mem_Q
  | inr k =>
    exact hyp.structureConjugator_mul_conj_inv_mem
      (by rw [← hyp.coe_K]; exact k.1.2)

lemma orbitRepVal_ne_one (i : hyp.OrbitReprIndex) : hyp.orbitRepVal i ≠ 1 := by
  cases i with
  | inl i =>
    fin_cases i
    · exact hyp.distinguishedInvolution_ne_one
    · exact hyp.structureConjugator_ne_one
    · exact inv_ne_one.mpr hyp.structureConjugator_ne_one
  | inr k =>
    exact hyp.structureConjugator_mul_conj_inv_ne_one
      (by rw [← hyp.coe_K]; exact k.1.2) (fun h => k.2 (Subtype.ext h))

lemma orbitRepVal_mem_orbitReprSet (i : hyp.OrbitReprIndex) :
    hyp.orbitRepVal i ∈ hyp.orbitReprSet := by
  cases i with
  | inl i =>
    refine Or.inl ?_
    fin_cases i
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  | inr k =>
    exact Or.inr ⟨(k : G), k.1.2, (fun h => k.2 (Subtype.ext h)), rfl⟩

/-- `|K#| = |K| − 1`. -/
lemma card_K_ne_one : Nat.card {k : ↥hyp.K // k ≠ 1} = Nat.card ↥hyp.K - 1 := by
  classical
  have h := Nat.card_congr (Equiv.optionSubtypeNe (1 : ↥hyp.K))
  rw [Finite.card_option] at h
  omega

/-- **The counting identity** `(|K#| + 3) · |K| + 1 = |Q|` of Peterfalvi
Part II, Ch. III §2, p. 118, in case (b): there `|Q| = q²` and `|K| = q − 1`,
so the left-hand side is `(q + 1)(q − 1) + 1 = q²`. -/
lemma card_orbitReprIndex_mul_card_K_succ
    (hQcard : Nat.card ↥hyp.Q = Nat.card ↥hyp.Q0 ^ 2) :
    Nat.card hyp.OrbitReprIndex * Nat.card ↥hyp.K + 1 = Nat.card ↥hyp.Q := by
  have hKcard : Nat.card ↥hyp.K = Nat.card ↥hyp.Q0 - 1 :=
    hyp.card_K_eq_card_Q0_sub_one
  have hQ0 : 2 ≤ Nat.card ↥hyp.Q0 := hyp.two_le_card_Q0
  have hidx : Nat.card hyp.OrbitReprIndex = 3 + (Nat.card ↥hyp.K - 1) := by
    rw [OrbitReprIndex, Nat.card_sum, hyp.card_K_ne_one, Nat.card_eq_fintype_card,
      Fintype.card_fin]
  obtain ⟨d, hd⟩ : ∃ d, Nat.card ↥hyp.Q0 = d + 2 := ⟨Nat.card ↥hyp.Q0 - 2, by omega⟩
  have hK : Nat.card ↥hyp.K = d + 1 := by rw [hKcard, hd]; omega
  have hidx' : Nat.card hyp.OrbitReprIndex = d + 3 := by rw [hidx, hK]; omega
  have hsq : (d + 2) ^ 2 = d * d + 4 * d + 4 := by ring
  have hprod : (d + 3) * (d + 1) = d * d + 4 * d + 3 := by ring
  rw [hidx', hK, hQcard, hd, hsq, hprod]

end Hypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
