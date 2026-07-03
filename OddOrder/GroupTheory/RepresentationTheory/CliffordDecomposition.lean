/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.CanonicalCharacterExtension
import OddOrder.GroupTheory.RepresentationTheory.GallagherDecomposition
import OddOrder.GroupTheory.RepresentationTheory.CliffordCorrespondence

/-!
# The constructive Clifford decomposition (Peterfalvi (1.7)(b))

**Peterfalvi, _Character Theory for the Odd Order Theorem_, Lemma 1.7(b), constructive
form**: let `H ⊴ L` and let `θ ∈ Irr(H)` have inertia group `T = I_L(θ)` with `T/H`
abelian and `gcd([T:H], o(θ)·θ(1)) = 1`.  Then

  `Ind_H^L θ = ∑_{β ∈ Hom(T/H, ℂˣ)} Ind_T^L (χ·Inf(β))`,

where `χ ∈ Irr(T)` is an extension of `θ` to its inertia group, and **every summand is
irreducible** of degree `[L:T]·θ(1)`.

This assembles the three generic ingredients of issue 9002:

* **(G1)** the coprime extension theorem (Isaacs 8.16,
  `IsIrreducibleCharacter.exists_extension_of_forall_conjBy_eq`) supplies `χ`;
* **(G2)** the Gallagher decomposition (Isaacs 6.17 coprime abelian case,
  `induce_eq_sum_mul_linearClassFunction`) decomposes `Ind_H^T θ = ∑_β χ·Inf(β)`;
* **(G3)** the Clifford correspondence (Isaacs 6.11,
  `isIrreducibleCharacter_induce_of_liesOver_of_inertia_eq`) makes each `Ind_T^L (χ·Inf β)`
  irreducible;

together with induction in stages (`induce_induce_subgroupOf`).

The multiplicity-one/distinctness packaging (the summands are pairwise distinct, by the
norm count `⟨Ind_H^L θ, Ind_H^L θ⟩ = [T:H]`) is the next layer; the type-I application
(Peterfalvi §8, `typeI_induced_char_constituents`) adds the support and non-reality
bookkeeping on top.

## Main result

* `exists_extension_induce_eq_sum_induce_mul` — the decomposition above.

## References

* Peterfalvi §3 (1.7)(b); Isaacs 6.11/6.17/8.16.  Issue 9002.
-/

namespace OddOrder.RepresentationTheory

variable {L : Type*} [Group L] [Fintype L] [Invertible (Nat.card L : ℂ)]

open scoped commutatorElement in
/-- **The constructive Clifford decomposition (Peterfalvi (1.7)(b))**.  Let `H ⊴ L`, let
`θ ∈ Irr(H)` have inertia group exactly `T` with `T/H` abelian (elementwise commutator
hypothesis), degree `d`, and `gcd([T:H], o(θ)·d) = 1`.  Then there is an extension
`χ ∈ Irr(T)` of (the transport of) `θ` such that

  `Ind_H^L θ = ∑_{β ∈ Hom(T/H, ℂˣ)} Ind_T^L (χ·Inf(β))`

with **every summand irreducible**.  Each summand has degree `[L:T]·d` by
`ClassFunction.induce_apply_one`. -/
theorem exists_extension_induce_eq_sum_induce_mul
    {H T : Subgroup L} [H.Normal] [(H.subgroupOf T).Normal] (hHT : H ≤ T)
    [Invertible (Nat.card ↥H : ℂ)] [Invertible (Nat.card ↥T : ℂ)]
    [Invertible (Nat.card ↥(H.subgroupOf T) : ℂ)]
    [Fintype ((↥T ⧸ H.subgroupOf T) →* ℂˣ)]
    {θ : ClassFunction ↥H ℂ} (hθ : IsIrreducibleCharacter θ)
    (hinertia : ClassFunction.inertia (G := L) θ = T)
    (hab : ∀ x y : ↥T, ⁅x, y⁆ ∈ H.subgroupOf T)
    {d : ℕ} (hd : θ 1 = (d : ℂ))
    (hcop : Nat.Coprime (H.subgroupOf T).index (orderOf hθ.determinant * d)) :
    ∃ (χ : ClassFunction ↥T ℂ) (_ : IsIrreducibleCharacter χ),
      ClassFunction.restrict (H.subgroupOf T) χ
          = ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hHT).toMonoidHom θ ∧
        ClassFunction.induce H θ
          = ∑ β : (↥T ⧸ H.subgroupOf T) →* ℂˣ,
              ClassFunction.induce T
                (χ * linearClassFunction (β.comp (QuotientGroup.mk' (H.subgroupOf T)))) ∧
        ∀ β : (↥T ⧸ H.subgroupOf T) →* ℂˣ,
          IsIrreducibleCharacter (ClassFunction.induce T
            (χ * linearClassFunction (β.comp (QuotientGroup.mk' (H.subgroupOf T))))) := by
  classical
  letI : Fintype ↥T := Fintype.ofFinite _
  letI : Fintype ↥(H.subgroupOf T) := Fintype.ofFinite _
  -- the transported character `θ'` and its properties
  set θ' : ClassFunction ↥(H.subgroupOf T) ℂ :=
    ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hHT).toMonoidHom θ with hθ'def
  have hθ' : IsIrreducibleCharacter θ' :=
    IsIrreducibleCharacter.compHom_of_surjective
      (Subgroup.subgroupOfEquivOfLe hHT).surjective hθ
  -- `θ'` is `T`-invariant (full inertia)
  have hinvT : ∀ t : ↥T, ClassFunction.conjBy ((t : L)) θ = θ := fun t => by
    have hmem : (t : L) ∈ ClassFunction.inertia (G := L) θ := by
      rw [hinertia]
      exact t.2
    exact (ClassFunction.mem_inertia).mp hmem
  have hinertia' : ClassFunction.inertia (G := ↥T) θ' = ⊤ :=
    inertia_compHom_subgroupOfEquivOfLe_eq_top hHT hinvT
  have hinv' : ∀ y : ↥T, ClassFunction.conjBy y θ' = θ' := fun y => by
    have hmem : y ∈ ClassFunction.inertia (G := ↥T) θ' := by
      rw [hinertia']
      exact Subgroup.mem_top y
    exact (ClassFunction.mem_inertia).mp hmem
  -- degree and determinantal order transport
  have hd' : θ' 1 = (d : ℂ) := by
    rw [hθ'def, ClassFunction.compHom_apply, map_one, hd]
  have hodet : orderOf hθ'.determinant = orderOf hθ.determinant := by
    rw [hθ.determinant_compHom (Subgroup.subgroupOfEquivOfLe hHT).toMonoidHom hθ']
    exact orderOf_monoidHom_comp_of_surjective _
      (Subgroup.subgroupOfEquivOfLe hHT).surjective
  -- (G1): extend `θ'` to `χ ∈ Irr(T)`
  obtain ⟨χ, hχ, hres, -⟩ :=
    hθ'.exists_extension_of_forall_conjBy_eq hinv' hab hd'
      (by rw [hodet]; exact hcop)
  refine ⟨χ, hχ, hres, ?_, ?_⟩
  · -- the decomposition, by stages + Gallagher + linearity
    have hstages := induce_induce_subgroupOf (M := L) hHT θ
    -- (G2) at the inertia group
    have hgal := induce_eq_sum_mul_linearClassFunction (K := ↥T) (H := H.subgroupOf T)
      hθ' hinv' hab hχ hres hd'
      (Nat.Coprime.coprime_dvd_right (dvd_mul_left d _) hcop)
    -- push the sum through `Ind_T^L`
    have hindsum : ∀ (s : Finset ((↥T ⧸ H.subgroupOf T) →* ℂˣ))
        (F : ((↥T ⧸ H.subgroupOf T) →* ℂˣ) → ClassFunction ↥T ℂ),
        ClassFunction.induce T (∑ β ∈ s, F β)
          = ∑ β ∈ s, ClassFunction.induce T (F β) := by
      intro s F
      induction s using Finset.induction_on with
      | empty => simp
      | insert a s ha ih =>
          rw [Finset.sum_insert ha, Finset.sum_insert ha, ClassFunction.induce_add, ih]
    calc ClassFunction.induce H θ
        = ClassFunction.induce T (ClassFunction.induce (H.subgroupOf T) θ') := hstages.symm
      _ = ClassFunction.induce T (∑ β : (↥T ⧸ H.subgroupOf T) →* ℂˣ,
            χ * linearClassFunction (β.comp (QuotientGroup.mk' (H.subgroupOf T)))) := by
          rw [hgal]
      _ = ∑ β : (↥T ⧸ H.subgroupOf T) →* ℂˣ,
            ClassFunction.induce T
              (χ * linearClassFunction (β.comp (QuotientGroup.mk' (H.subgroupOf T)))) :=
          hindsum _ _
  · -- each summand is irreducible, by the Clifford correspondence (G3)
    intro β
    -- the twist is irreducible and restricts to `θ'`
    have hψirr : IsIrreducibleCharacter
        (χ * linearClassFunction (β.comp (QuotientGroup.mk' (H.subgroupOf T)))) :=
      isIrreducibleCharacter_mul_linearClassFunction hχ _
    have hψres : ClassFunction.restrict (H.subgroupOf T)
        (χ * linearClassFunction (β.comp (QuotientGroup.mk' (H.subgroupOf T)))) = θ' := by
      rw [ClassFunction.restrict_mul_of_apply_eq_one χ _
        (fun x => linearClassFunction_comp_mk'_apply_eq_one β x.2), hres]
    -- apply Isaacs 6.11 with `ψ = χ·Inf(β)`
    have h611 := isIrreducibleCharacter_induce_of_liesOver_of_inertia_eq (G := L) hHT hθ
      hinertia
      (⟨χ * linearClassFunction (β.comp (QuotientGroup.mk' (H.subgroupOf T))), hψirr⟩ :
        IrreducibleCharacter ↥T)
      (by
        change ClassFunction.restrictionMultiplicity (H.subgroupOf T)
          (χ * linearClassFunction (β.comp (QuotientGroup.mk' (H.subgroupOf T)))) θ' ≠ 0
        rw [ClassFunction.restrictionMultiplicity_def, hψres, hθ'.inner_self_eq_one]
        exact one_ne_zero)
    exact h611

end OddOrder.RepresentationTheory
