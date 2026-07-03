/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.CliffordSingleOrbit

/-!
# The Clifford correspondence (toward Isaacs 6.11)

**Isaacs, _Character Theory of Finite Groups_, Theorem 6.11 (Clifford correspondence),
irreducibility half**: let `H ⊴ G`, `θ ∈ Irr(H)` with inertia group `T = I_G(θ)`, and let
`ψ ∈ Irr(T)` lie over `θ`.  Then `Ind_T^G ψ` is **irreducible**.

The proof is the θ-part counting argument (no Mackey formula needed): for any irreducible
constituent `χ` of `Ind_T^G ψ` with multiplicity `m = ⟨Ind ψ, χ⟩ ≥ 1`,

* `ψ(1) = e·θ(1)` where `e = ⟨Res_H ψ, θ⟩` (single-orbit degree formula at `(T, H)` —
  `θ` is `T`-invariant);
* `⟨Res_H χ, θ⟩ ≥ m·e` (expand `Res_T χ` into irreducibles of `T` and restrict further:
  every term contributes non-negatively to the `θ`-multiplicity);
* `χ(1) = ⟨Res_H χ, θ⟩·[G:T]·θ(1) ≥ m·e·[G:T]·θ(1) = m·(Ind ψ)(1)` (single-orbit degree
  formula at `(G, H)`, using `I_G(θ) = T`), while `χ(1) ≤ (Ind ψ)(1)`
  (`apply_one_le_induce_apply_one_of_liesOver`); hence `m = 1` and the degrees agree;
* degree exhaustion (`induce_eq_coe_of_inner_eq_one_of_apply_one_eq`, this file):
  a multiplicity-one constituent of full degree exhausts the induced character.

This file currently provides the **degree-exhaustion capstone**; the θ-part lower bound
requires the `inner`-transport lemma `inner_compHom_of_mulEquiv` and the constituent
decomposition, whose relocation from `S08_CaseBCoherence2.lean` into a shared leaf is
requested in issue 9005.

This is the (G3)/6.11 step of the constructive Clifford decomposition for Peterfalvi
(1.7)(b) (issue 9002): combined with the extension theorem (Isaacs 8.16,
`CanonicalCharacterExtension`) and the Gallagher decomposition (`GallagherDecomposition`),
it yields the multiplicity-one equal-degree decomposition of `Ind_H^L θ` for a type-I
maximal subgroup.

## Main results

* `induce_eq_coe_of_inner_eq_one_of_apply_one_eq` — a multiplicity-one irreducible
  constituent of the same degree exhausts the induced character.

## References

* I. M. Isaacs, *Character Theory of Finite Groups*, Academic Press 1976, Thm 6.11.
* Peterfalvi §3 (1.7); issue 9002 (G3), issue 9005.
-/

namespace OddOrder.RepresentationTheory

variable {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]

open scoped ComplexOrder in
/-- **Degree exhaustion for an induced character**: if `χ ∈ Irr(G)` occurs in `Ind_I^G ψ`
with multiplicity exactly `1` and `(Ind_I^G ψ)(1) = χ(1)`, then `Ind_I^G ψ = χ` — in
particular the induced character is irreducible.

Expanding `Ind ψ = ∑_η ⟨Ind ψ, η⟩ • η` (Fourier), every coefficient is a non-negative
integer (`⟨Ind ψ, η⟩ = ⟨Res η, ψ⟩` by Frobenius reciprocity); evaluating at `1`, the
`χ`-term already accounts for the full degree, so all other coefficients vanish.  This is
the final step of the Clifford correspondence irreducibility (Isaacs 6.11). -/
theorem induce_eq_coe_of_inner_eq_one_of_apply_one_eq
    {I : Subgroup G} [Invertible (Nat.card ↥I : ℂ)]
    (ψ : IrreducibleCharacter ↥I) (χ : IrreducibleCharacter G)
    (h1 : ClassFunction.inner (ClassFunction.induce I (ψ : ClassFunction ↥I ℂ))
        (χ : ClassFunction G ℂ) = 1)
    (hdeg : ClassFunction.induce I (ψ : ClassFunction ↥I ℂ) (1 : G)
        = (χ : ClassFunction G ℂ) (1 : G)) :
    ClassFunction.induce I (ψ : ClassFunction ↥I ℂ) = (χ : ClassFunction G ℂ) := by
  classical
  letI : Fintype ↥I := Fintype.ofFinite _
  haveI : Finite (IrreducibleCharacter G) := finite_irreducibleCharacter (G := G)
  letI : Fintype (IrreducibleCharacter G) := Fintype.ofFinite _
  -- every Fourier coefficient of `Ind ψ` is a (real, non-negative) restriction multiplicity
  have hcoeff : ∀ η : IrreducibleCharacter G,
      ClassFunction.inner (ClassFunction.induce I (ψ : ClassFunction ↥I ℂ))
          (η : ClassFunction G ℂ)
        = ClassFunction.restrictionMultiplicity I (η : ClassFunction G ℂ)
            (ψ : ClassFunction ↥I ℂ) := by
    intro η
    obtain ⟨k, hk⟩ := IrreducibleCharacter.restrictionMultiplicity_natCast (H := I) η ψ
    rw [ClassFunction.inner_induce_eq_inner_restrict I (ψ : ClassFunction ↥I ℂ)
        (η : ClassFunction G ℂ),
      inner_conj_symm (ClassFunction.restrict I (η : ClassFunction G ℂ))
        (ψ : ClassFunction ↥I ℂ)]
    change star (ClassFunction.restrictionMultiplicity I (η : ClassFunction G ℂ)
        (ψ : ClassFunction ↥I ℂ)) = _
    rw [hk, star_natCast]
  -- Fourier expansion of `Ind ψ`, evaluated at `1`
  have hsumapp : ∀ (s : Finset (IrreducibleCharacter G))
      (F : IrreducibleCharacter G → ClassFunction G ℂ),
      (∑ η ∈ s, F η) (1 : G) = ∑ η ∈ s, (F η) (1 : G) := by
    intro s F
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha, ClassFunction.add_apply, ih]
  have hexp := sum_inner_irreducibleCharacter_smul (G := G)
    (ClassFunction.induce I (ψ : ClassFunction ↥I ℂ))
  have key := congrArg (fun f : ClassFunction G ℂ => f (1 : G)) hexp
  simp only [hsumapp, ClassFunction.smul_apply] at key
  -- split off the `χ`-term: it already equals the full degree
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ χ), h1, one_mul, hdeg] at key
  have hrest : ∑ η ∈ Finset.univ.erase χ,
      ClassFunction.inner (ClassFunction.induce I (ψ : ClassFunction ↥I ℂ))
          (η : ClassFunction G ℂ) * (η : ClassFunction G ℂ) (1 : G) = 0 := by
    have := key
    linear_combination this
  -- each remaining summand is non-negative, so each vanishes
  have hnn : ∀ η ∈ Finset.univ.erase χ,
      (0 : ℂ) ≤ ClassFunction.inner (ClassFunction.induce I (ψ : ClassFunction ↥I ℂ))
          (η : ClassFunction G ℂ) * (η : ClassFunction G ℂ) (1 : G) := by
    intro η _
    have h0 : (0 : ℂ) ≤ ClassFunction.inner
        (ClassFunction.induce I (ψ : ClassFunction ↥I ℂ)) (η : ClassFunction G ℂ) := by
      rw [hcoeff η]
      exact ClassFunction.restrictionMultiplicity_nonneg I η.isIrreducible ψ.isIrreducible
    obtain ⟨dη, _, hdη⟩ := irreducibleCharacter_apply_one_eq_pos_natCast η
    rw [hdη]
    exact mul_nonneg h0 (by positivity)
  have hzero : ∀ η ∈ Finset.univ.erase χ,
      ClassFunction.inner (ClassFunction.induce I (ψ : ClassFunction ↥I ℂ))
          (η : ClassFunction G ℂ) * (η : ClassFunction G ℂ) (1 : G) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hrest
  have hcoeff_zero : ∀ η ∈ Finset.univ.erase χ,
      ClassFunction.inner (ClassFunction.induce I (ψ : ClassFunction ↥I ℂ))
          (η : ClassFunction G ℂ) = 0 := by
    intro η hη
    obtain ⟨dη, hdpos, hdη⟩ := irreducibleCharacter_apply_one_eq_pos_natCast η
    have h0 := hzero η hη
    rw [hdη] at h0
    exact (mul_eq_zero.mp h0).resolve_right
      (Nat.cast_ne_zero.mpr hdpos.ne')
  -- collapse the expansion to the `χ`-term
  conv_lhs => rw [← hexp]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ χ), h1, one_smul,
    Finset.sum_eq_zero fun η hη => by rw [hcoeff_zero η hη, zero_smul], add_zero]

end OddOrder.RepresentationTheory
