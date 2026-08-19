/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.StructureOfH.LinearCharacter
import OddOrder.GroupTheory.RepresentationTheory.PermutationCharacter
import OddOrder.GroupTheory.RepresentationTheory.CharacterProduct

/-!
# Peterfalvi Part II, Ch. III: `⟨Ind λ, Ind λ⟩ = 2` (Theorem C, step (7))

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Part II, Ch. III, §1, p. 115:

> It follows from the definition of `Ind_H^G` that, for `x ∈ H`,
> `(Ind_H^G λ)(x) = λ(x)(Ind_H^G 1_H)(x)`, whence
> `(Ind_H^G λ, Ind_H^G λ) = (Res_H^G Ind_H^G λ, λ) = (λ Res_H^G Ind_H^G 1_H, λ)
> = (Res_H^G Ind_H^G 1_H, 1_H) = (Ind_H^G 1_H, Ind_H^G 1_H) = 2`.

The value identity applies step (6) (`apply_eq_of_isConj`) to each summand of
the induction formula.  The norm chain is Frobenius reciprocity
(`inner_induce_eq_inner_restrict`), unimodularity of the linear character
(`IsIrreducibleCharacter.apply_mul_star_self_eq_one`), and the norm of the
permutation character of the doubly transitive action on `Ω`
(`inner_induce_trivial_of_eq_stabilizer`).
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki

open OddOrder.RepresentationTheory

universe uG uΩ

namespace SecondCaseHypothesis

variable {G : Type uG} {Ω : Type uΩ} [Group G] [MulAction G Ω] [Finite G]
  (sc : SecondCaseHypothesis G Ω)

/-- **Peterfalvi Part II, Ch. III, Theorem C, step (7), value identity**
(p. 115): for `x ∈ H`, `(Ind_H^G λ)(x) = λ(x)·(Ind_H^G 1_H)(x)`.

Each summand of the induction formula with conjugator `g` evaluates `λ` at the
`G`-conjugate `g⁻¹xg ∈ H` of `x`, which equals `λ(x)` by step (6)
(`apply_eq_of_isConj`); so `λ(x)` factors out of the sum, leaving the induced
trivial character. -/
theorem induce_apply_coe [Fintype G]
    [Invertible (Nat.card ↥sc.toHypothesis.H : ℂ)]
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hQ1 : sc.toHypothesis.Q1 ≠ ⊥)
    {θ : ClassFunction ↥sc.toHypothesis.H ℂ} (hθ : IsIrreducibleCharacter θ)
    (hdeg : (θ : ↥sc.toHypothesis.H → ℂ) 1 = 1)
    (hker : ((sc.toHypothesis.QK.subgroupOf sc.toHypothesis.H :
      Subgroup ↥sc.toHypothesis.H) : Set ↥sc.toHypothesis.H) ⊆
        OddOrder.Peterfalvi.S03.characterKernel θ)
    (x : ↥sc.toHypothesis.H) :
    ClassFunction.induce sc.toHypothesis.H θ (x : G)
      = (θ : ↥sc.toHypothesis.H → ℂ) x
        * ClassFunction.induce sc.toHypothesis.H
            (trivialClassFunction ↥sc.toHypothesis.H) (x : G) := by
  classical
  have hsum : (∑ g : G, ClassFunction.induceTerm sc.toHypothesis.H θ g (x : G))
      = (θ : ↥sc.toHypothesis.H → ℂ) x
        * ∑ g : G, ClassFunction.induceTerm sc.toHypothesis.H
            (trivialClassFunction ↥sc.toHypothesis.H) g (x : G) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    by_cases hg : g⁻¹ * (x : G) * g ∈ sc.toHypothesis.H
    · rw [ClassFunction.induceTerm_of_mem θ hg,
        ClassFunction.induceTerm_of_mem (trivialClassFunction ↥sc.toHypothesis.H) hg,
        trivialClassFunction_apply, mul_one]
      exact (sc.apply_eq_of_isConj ind hQ1 hθ hdeg hker
        (x := x) (y := ⟨g⁻¹ * (x : G) * g, hg⟩) (g := g⁻¹)
        (by rw [inv_inv])).symm
    · rw [ClassFunction.induceTerm_of_not_mem θ hg,
        ClassFunction.induceTerm_of_not_mem (trivialClassFunction ↥sc.toHypothesis.H) hg,
        mul_zero]
  rw [ClassFunction.induce_apply, ClassFunction.induce_apply, hsum]
  ring

/-- **Peterfalvi Part II, Ch. III, Theorem C, step (7)** (p. 115):
`⟨Ind_H^G λ, Ind_H^G λ⟩ = 2`.

The chain `(Ind λ, Ind λ) = (λ·Res Ind 1_H, λ) = (Res Ind 1_H, 1_H)
= (Ind 1_H, Ind 1_H) = 2`: Frobenius reciprocity twice, the value identity
`induce_apply_coe`, unimodularity of `λ`, and the norm of the permutation
character of the doubly transitive action of `G` on `Ω`. -/
theorem inner_induce_self_eq_two [Fintype G] [Invertible (Nat.card G : ℂ)]
    [Invertible (Nat.card ↥sc.toHypothesis.H : ℂ)]
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hQ1 : sc.toHypothesis.Q1 ≠ ⊥)
    {θ : ClassFunction ↥sc.toHypothesis.H ℂ} (hθ : IsIrreducibleCharacter θ)
    (hdeg : (θ : ↥sc.toHypothesis.H → ℂ) 1 = 1)
    (hker : ((sc.toHypothesis.QK.subgroupOf sc.toHypothesis.H :
      Subgroup ↥sc.toHypothesis.H) : Set ↥sc.toHypothesis.H) ⊆
        OddOrder.Peterfalvi.S03.characterKernel θ) :
    ClassFunction.inner (ClassFunction.induce sc.toHypothesis.H θ)
      (ClassFunction.induce sc.toHypothesis.H θ) = 2 := by
  classical
  have : Fintype ↥sc.toHypothesis.H := Fintype.ofFinite _
  have : Finite Ω := sc.toHypothesis.finite_Omega
  have : Nontrivial Ω := by
    rw [← Finite.one_lt_card_iff_nontrivial, sc.toHypothesis.card_Omega]
    have := Nat.card_pos (α := ↥sc.toHypothesis.Q)
    omega
  rw [ClassFunction.inner_induce_eq_inner_restrict]
  have key : ClassFunction.inner θ
      (ClassFunction.restrict sc.toHypothesis.H
        (ClassFunction.induce sc.toHypothesis.H θ))
      = ClassFunction.inner (trivialClassFunction ↥sc.toHypothesis.H)
          (ClassFunction.restrict sc.toHypothesis.H
            (ClassFunction.induce sc.toHypothesis.H
              (trivialClassFunction ↥sc.toHypothesis.H))) := by
    rw [ClassFunction.inner_eq_inv_card_mul_innerSum,
      ClassFunction.inner_eq_inv_card_mul_innerSum]
    congr 1
    unfold ClassFunction.innerSum
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [ClassFunction.restrict_apply, ClassFunction.restrict_apply,
      sc.induce_apply_coe ind hQ1 hθ hdeg hker x, star_mul',
      trivialClassFunction_apply, one_mul, ← mul_assoc,
      hθ.apply_mul_star_self_eq_one hdeg x, one_mul]
  rw [key, ← ClassFunction.inner_induce_eq_inner_restrict]
  exact ClassFunction.inner_induce_trivial_of_eq_stabilizer
    sc.toHypothesis.H_def sc.toHypothesis.doubly_transitive

/-- **Peterfalvi Part II, Ch. III, Theorem C, step (8)** (p. 116):
`Ind_H^G λ = f₁ + f₂` with `f₁, f₂ ∈ Irr(G)` distinct and non-principal.

`Ind λ ∈ ℤ[Irr G]` has norm `2` (step (7)), so it is a signed sum `±f₁ ± f₂`
of two distinct irreducibles; both signs are `+` because
`⟨Ind λ, fᵢ⟩ = ⟨λ, Res fᵢ⟩ ≥ 0` (Frobenius reciprocity and multiplicities of
the genuine restriction); and `fᵢ ≠ 1_G` because
`⟨Ind λ, 1_G⟩ = ⟨λ, 1_H⟩ = 0` while `f₁ = 1_G` would force that inner product
to be `1`. -/
theorem exists_induce_eq_add_irreducible [Fintype G]
    [Invertible (Nat.card G : ℂ)]
    [Invertible (Nat.card ↥sc.toHypothesis.H : ℂ)]
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hQ1 : sc.toHypothesis.Q1 ≠ ⊥)
    {θ : ClassFunction ↥sc.toHypothesis.H ℂ} (hθ : IsIrreducibleCharacter θ)
    (hdeg : (θ : ↥sc.toHypothesis.H → ℂ) 1 = 1)
    (hker : ((sc.toHypothesis.QK.subgroupOf sc.toHypothesis.H :
      Subgroup ↥sc.toHypothesis.H) : Set ↥sc.toHypothesis.H) ⊆
        OddOrder.Peterfalvi.S03.characterKernel θ)
    (hne : θ ≠ trivialClassFunction ↥sc.toHypothesis.H) :
    ∃ f₁ f₂ : ClassFunction G ℂ,
      IsIrreducibleCharacter f₁ ∧ IsIrreducibleCharacter f₂ ∧ f₁ ≠ f₂ ∧
      f₁ ≠ trivialClassFunction G ∧ f₂ ≠ trivialClassFunction G ∧
      ClassFunction.induce sc.toHypothesis.H θ = f₁ + f₂ := by
  classical
  have : Fintype ↥sc.toHypothesis.H := Fintype.ofFinite _
  set Φ := ClassFunction.induce sc.toHypothesis.H θ with hΦ
  have hZ : Φ ∈ ZIrr G := ClassFunction.induce_mem_ZIrr _ hθ.mem_ZIrr
  have h2 : ClassFunction.inner Φ Φ = 2 :=
    sc.inner_induce_self_eq_two ind hQ1 hθ hdeg hker
  obtain ⟨α, β, εα, εβ, hα, hβ, hαβ, hεα, hεβ, hrepr⟩ :=
    exists_signed_pair_of_mem_ZIrr_inner_self_eq_two hZ h2
  -- `⟨Φ, γ⟩` is a non-negative integer for every irreducible `γ`
  have hnn : ∀ γ : ClassFunction G ℂ, IsIrreducibleCharacter γ →
      ∃ k : ℕ, ClassFunction.inner Φ γ = (k : ℂ) := by
    intro γ hγ
    rw [hΦ, ClassFunction.inner_induce_eq_inner_restrict]
    have hres : IsCharacter (ClassFunction.restrict sc.toHypothesis.H γ) :=
      OddOrder.Peterfalvi.S08.isCharacter_restrict hγ.isCharacter _
    obtain ⟨k, hk⟩ := hres.exists_natCast_inner_irreducible hθ
    exact ⟨k, by
      rw [OddOrder.RepresentationTheory.inner_conj_symm, hk, star_natCast]⟩
  -- orthonormality: `⟨Φ, α⟩ = εα` and `⟨Φ, β⟩ = εβ`
  have hinnerα : ClassFunction.inner Φ α = (εα : ℂ) := by
    rw [hrepr, ClassFunction.inner_add_left, ClassFunction.inner_smul_left,
      ClassFunction.inner_smul_left,
      OddOrder.RepresentationTheory.irr_cf_inner
        (mem_irreducibleCharacters.mpr hα) (mem_irreducibleCharacters.mpr hα),
      OddOrder.RepresentationTheory.irr_cf_inner
        (mem_irreducibleCharacters.mpr hβ) (mem_irreducibleCharacters.mpr hα),
      if_pos rfl, if_neg (Ne.symm hαβ), mul_one, mul_zero, add_zero]
  have hinnerβ : ClassFunction.inner Φ β = (εβ : ℂ) := by
    rw [hrepr, ClassFunction.inner_add_left, ClassFunction.inner_smul_left,
      ClassFunction.inner_smul_left,
      OddOrder.RepresentationTheory.irr_cf_inner
        (mem_irreducibleCharacters.mpr hα) (mem_irreducibleCharacters.mpr hβ),
      OddOrder.RepresentationTheory.irr_cf_inner
        (mem_irreducibleCharacters.mpr hβ) (mem_irreducibleCharacters.mpr hβ),
      if_neg hαβ, if_pos rfl, mul_one, mul_zero, zero_add]
  -- the signs are `+1`
  have hsign : ∀ (γ : ClassFunction G ℂ) (ε : ℤ), IsIrreducibleCharacter γ →
      ClassFunction.inner Φ γ = (ε : ℂ) → (ε = 1 ∨ ε = -1) → ε = 1 := by
    intro γ ε hγ hinner hcases
    rcases hcases with h | h
    · exact h
    · exfalso
      obtain ⟨k, hk⟩ := hnn γ hγ
      rw [hinner, h] at hk
      have hint : ((-1 : ℤ) : ℂ) = ((k : ℤ) : ℂ) := by push_cast at hk ⊢; exact hk
      have := Int.cast_injective hint
      omega
  have hεα1 : εα = 1 := hsign α εα hα hinnerα hεα
  have hεβ1 : εβ = 1 := hsign β εβ hβ hinnerβ hεβ
  rw [hεα1] at hinnerα
  rw [hεβ1] at hinnerβ
  -- `⟨Φ, 1_G⟩ = ⟨λ, 1_H⟩ = 0`
  have htriv : ClassFunction.inner Φ (trivialClassFunction G) = 0 := by
    rw [hΦ, ClassFunction.induce_inner_trivial,
      OddOrder.RepresentationTheory.irr_cf_inner
        (mem_irreducibleCharacters.mpr hθ) trivialClassFunction_isIrreducible,
      if_neg hne]
  refine ⟨α, β, hα, hβ, hαβ, fun h => ?_, fun h => ?_, ?_⟩
  · rw [h, htriv] at hinnerα
    norm_num at hinnerα
  · rw [h, htriv] at hinnerβ
    norm_num at hinnerβ
  · rw [hrepr, hεα1, hεβ1, Int.cast_one, one_smul, one_smul]

end SecondCaseHypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
