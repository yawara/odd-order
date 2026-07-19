/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.CliffordSingleOrbit
import OddOrder.GroupTheory.RepresentationTheory.InflationCharacter
import OddOrder.GroupTheory.RepresentationTheory.InducedTransport

/-!
# The Clifford correspondence (toward Isaacs 6.11)

**Isaacs, _Character Theory of Finite Groups_, Theorem 6.11 (Clifford correspondence),
irreducibility half**: let `H ⊴ G`, `θ ∈ Irr(H)` with inertia group `T = I_G(θ)`, and let
`ψ ∈ Irr(T)` lie over `θ`.  Then `Ind_T^G ψ` is **irreducible**.

The same θ-part count gives the **injectivity half** (`ψ ↦ Ind_T^G ψ` is injective on the
characters of `T` lying over `θ`), and the two together with induction in stages assemble
**Peterfalvi (1.7.a)** verbatim: for `Ind_H^T θ = ∑ᵢ eᵢψᵢ` with distinct `ψᵢ ∈ Irr(T)`, the
`χᵢ = Ind_T^G ψᵢ` are distinct irreducible characters of `G` and `Ind_H^G θ = ∑ᵢ eᵢχᵢ`.

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

This is the (G3)/6.11 step of the constructive Clifford decomposition for Peterfalvi
(1.7)(b) (issue 9002): combined with the extension theorem (Isaacs 8.16,
`CanonicalCharacterExtension`) and the Gallagher decomposition (`GallagherDecomposition`),
it yields the multiplicity-one equal-degree decomposition of `Ind_H^L θ` for a type-I
maximal subgroup.

## Main results

* `isIrreducibleCharacter_induce_of_liesOver_of_inertia_eq` — the Clifford correspondence
  irreducibility: `Ind_{I_G(θ)}^G ψ` is irreducible for `ψ ∈ Irr(I_G(θ))` over `θ`.
* `eq_of_induce_eq_induce_of_liesOver_of_inertia_eq` — the Clifford correspondence
  injectivity (Peterfalvi (1.7.a), distinctness half).
* `induce_eq_sum_smul_induce_of_inertia_eq` — Peterfalvi (1.7.a), the packaged statement.
* `restrictionMultiplicity_mul_le_restrictionMultiplicity` — the θ-part lower bound, and
  `sum_restrictionMultiplicity_mul_le_restrictionMultiplicity` its family form.
* `induce_eq_coe_of_inner_eq_one_of_apply_one_eq` — degree exhaustion: a multiplicity-one
  irreducible constituent of the same degree exhausts the induced character.

## References

* I. M. Isaacs, *Character Theory of Finite Groups*, Academic Press 1976, Thm 6.11.
* Peterfalvi §3 (1.7); issue 9002 (G3), issue 9005.
-/

namespace OddOrder.RepresentationTheory

variable {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]

omit [Fintype G] [Invertible (Nat.card G : ℂ)] in
/-- **Restriction in stages**: restricting to `T` and then to `H ≤ T` is restriction to `H`,
up to the transport `↥(H.subgroupOf T) ≃* ↥H`.  All three functions evaluate `φ` at the same
underlying element of `G`. -/
theorem ClassFunction.restrict_subgroupOf_restrict {k : Type*} [CommRing k]
    {H T : Subgroup G} (hHT : H ≤ T) (φ : ClassFunction G k) :
    ClassFunction.restrict (H.subgroupOf T) (ClassFunction.restrict T φ)
      = ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hHT).toMonoidHom
          (ClassFunction.restrict H φ) := by
  ext y
  rw [ClassFunction.restrict_apply, ClassFunction.restrict_apply, ClassFunction.compHom_apply,
    ClassFunction.restrict_apply]
  rfl

/-- **The multiplicity of `η` in `Ind_I^G ψ` is the restriction multiplicity `⟨Res_I η, ψ⟩`**
(Frobenius reciprocity, with the conjugation stripped by the real-valuedness of the
multiplicity). -/
theorem inner_induce_coe_eq_restrictionMultiplicity
    {I : Subgroup G} [Fintype ↥I] [Invertible (Nat.card ↥I : ℂ)]
    (ψ : IrreducibleCharacter ↥I) (η : IrreducibleCharacter G) :
    ClassFunction.inner (ClassFunction.induce I (ψ : ClassFunction ↥I ℂ))
        (η : ClassFunction G ℂ)
      = ClassFunction.restrictionMultiplicity I (η : ClassFunction G ℂ)
          (ψ : ClassFunction ↥I ℂ) := by
  obtain ⟨k, hk⟩ := IrreducibleCharacter.restrictionMultiplicity_natCast (H := I) η ψ
  rw [ClassFunction.inner_induce_eq_inner_restrict I (ψ : ClassFunction ↥I ℂ)
      (η : ClassFunction G ℂ),
    inner_conj_symm (ClassFunction.restrict I (η : ClassFunction G ℂ))
      (ψ : ClassFunction ↥I ℂ)]
  change star (ClassFunction.restrictionMultiplicity I (η : ClassFunction G ℂ)
      (ψ : ClassFunction ↥I ℂ)) = _
  rw [hk, star_natCast]

omit [Fintype G] [Invertible (Nat.card G : ℂ)] in
/-- **The transported character has full inertia group**: if `θ` is invariant under
conjugation by every element of `T`, then its transport `θ' = θ ∘ e` along
`e : ↥(H.subgroupOf T) ≃* ↥H` is invariant under all of `↥T`, i.e. `I_T(θ') = ⊤`.
In the Clifford correspondence `T = I_G(θ)`, so this applies verbatim. -/
theorem inertia_compHom_subgroupOfEquivOfLe_eq_top
    {H T : Subgroup G} [H.Normal] [(H.subgroupOf T).Normal] (hHT : H ≤ T)
    {θ : ClassFunction ↥H ℂ}
    (hinv : ∀ t : ↥T, ClassFunction.conjBy ((t : G)) θ = θ) :
    ClassFunction.inertia (G := ↥T)
        (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hHT).toMonoidHom θ) = ⊤ := by
  rw [Subgroup.eq_top_iff']
  intro t
  rw [ClassFunction.mem_inertia]
  ext h'
  have key := congrFun (congrArg (fun f : ClassFunction ↥H ℂ => (f : ↥H → ℂ)) (hinv t))
    (⟨((h' : ↥T) : G), h'.2⟩ : ↥H)
  calc (ClassFunction.conjBy t
        (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hHT).toMonoidHom θ)) h'
      = θ ⟨(t : G) * ((h' : ↥T) : G) * (t : G)⁻¹,
          ‹H.Normal›.conj_mem _ h'.2 (t : G)⟩ := by
        exact congrArg θ (Subtype.ext rfl)
    _ = θ ⟨((h' : ↥T) : G), h'.2⟩ := by
        exact (congrArg θ (Subtype.ext rfl)).trans key
    _ = (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hHT).toMonoidHom θ) h' := by
        exact congrArg θ (Subtype.ext rfl)

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
            (ψ : ClassFunction ↥I ℂ) :=
    fun η => inner_induce_coe_eq_restrictionMultiplicity ψ η
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

omit [Fintype G] [Invertible (Nat.card G : ℂ)] in
open scoped ComplexOrder in
/-- **The θ-part lower bound**: the multiplicity of `θ` in `Res_H χ` is at least
`⟨Res_T χ, ψ⟩ · ⟨Res_H ψ, θ⟩` for any `ψ ∈ Irr(T)` (with `H ≤ T` and the inner restriction
transported along `↥(H.subgroupOf T) ≃* ↥H`).

Expand `Res_T χ` into irreducibles of `T` and restrict once more: by
`ClassFunction.restrict_subgroupOf_restrict` and `inner_compHom_of_mulEquiv` the θ-multiplicity
of `χ` is `∑_ρ ⟨Res_T χ, ρ⟩·⟨Res ρ, θ'⟩`, a sum of products of non-negative integers, and the
`ψ`-term alone is the claimed bound.  This is the counting heart of Isaacs 6.11. -/
theorem restrictionMultiplicity_mul_le_restrictionMultiplicity
    {H T : Subgroup G} (hHT : H ≤ T)
    [Fintype ↥T] [Invertible (Nat.card ↥T : ℂ)]
    [Fintype ↥(H.subgroupOf T)] [Invertible (Nat.card ↥(H.subgroupOf T) : ℂ)]
    [Fintype ↥H] [Invertible (Nat.card ↥H : ℂ)]
    (χ : IrreducibleCharacter G) (ψ : IrreducibleCharacter ↥T)
    {θ : ClassFunction ↥H ℂ} (hθ : IsIrreducibleCharacter θ) :
    ClassFunction.restrictionMultiplicity T (χ : ClassFunction G ℂ) (ψ : ClassFunction ↥T ℂ)
        * ClassFunction.restrictionMultiplicity (H.subgroupOf T) (ψ : ClassFunction ↥T ℂ)
            (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hHT).toMonoidHom θ)
      ≤ ClassFunction.restrictionMultiplicity H (χ : ClassFunction G ℂ) θ := by
  classical
  haveI : Finite (IrreducibleCharacter ↥T) := finite_irreducibleCharacter (G := ↥T)
  letI : Fintype (IrreducibleCharacter ↥T) := Fintype.ofFinite _
  set θ' : ClassFunction ↥(H.subgroupOf T) ℂ :=
    ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hHT).toMonoidHom θ with hθ'
  have hθ'irr : IsIrreducibleCharacter θ' :=
    IsIrreducibleCharacter.compHom_of_surjective (Subgroup.subgroupOfEquivOfLe hHT).surjective hθ
  -- the H-level multiplicity, transported to `H.subgroupOf T`
  have h1 : ClassFunction.restrictionMultiplicity H (χ : ClassFunction G ℂ) θ
      = ClassFunction.inner (ClassFunction.restrict (H.subgroupOf T)
          (ClassFunction.restrict T (χ : ClassFunction G ℂ))) θ' := by
    rw [ClassFunction.restrict_subgroupOf_restrict hHT, hθ']
    exact (inner_compHom_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hHT)
      (ClassFunction.restrict H (χ : ClassFunction G ℂ)) θ).symm
  -- expand `Res_T χ` into irreducibles of `T` and push through
  have hres_sum : ∀ (s : Finset (IrreducibleCharacter ↥T))
      (F : IrreducibleCharacter ↥T → ClassFunction ↥T ℂ),
      ClassFunction.restrict (H.subgroupOf T) (∑ ρ ∈ s, F ρ)
        = ∑ ρ ∈ s, ClassFunction.restrict (H.subgroupOf T) (F ρ) := by
    intro s F
    induction s using Finset.induction_on with
    | empty =>
        ext y
        simp
    | insert a s ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha, ClassFunction.restrict_add, ih]
  have h2 : ClassFunction.inner (ClassFunction.restrict (H.subgroupOf T)
        (ClassFunction.restrict T (χ : ClassFunction G ℂ))) θ'
      = ∑ ρ : IrreducibleCharacter ↥T,
          ClassFunction.inner (ClassFunction.restrict T (χ : ClassFunction G ℂ))
              (ρ : ClassFunction ↥T ℂ)
            * ClassFunction.inner (ClassFunction.restrict (H.subgroupOf T)
                (ρ : ClassFunction ↥T ℂ)) θ' := by
    conv_lhs => rw [← sum_inner_irreducibleCharacter_smul (G := ↥T)
      (ClassFunction.restrict T (χ : ClassFunction G ℂ))]
    rw [hres_sum, inner_sum_left]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    rw [ClassFunction.restrict_smul, ClassFunction.inner_smul_left]
  -- every summand is a product of non-negative integers
  have hnn : ∀ ρ ∈ (Finset.univ : Finset (IrreducibleCharacter ↥T)),
      (0 : ℂ) ≤ ClassFunction.inner (ClassFunction.restrict T (χ : ClassFunction G ℂ))
          (ρ : ClassFunction ↥T ℂ)
        * ClassFunction.inner (ClassFunction.restrict (H.subgroupOf T)
            (ρ : ClassFunction ↥T ℂ)) θ' := by
    intro ρ _
    refine mul_nonneg ?_ ?_
    · exact ClassFunction.restrictionMultiplicity_nonneg T χ.isIrreducible ρ.isIrreducible
    · exact ClassFunction.restrictionMultiplicity_nonneg (H.subgroupOf T) ρ.isIrreducible hθ'irr
  -- the `ψ`-term is the claimed product
  calc ClassFunction.restrictionMultiplicity T (χ : ClassFunction G ℂ)
          (ψ : ClassFunction ↥T ℂ)
        * ClassFunction.restrictionMultiplicity (H.subgroupOf T) (ψ : ClassFunction ↥T ℂ) θ'
      ≤ ∑ ρ : IrreducibleCharacter ↥T,
          ClassFunction.inner (ClassFunction.restrict T (χ : ClassFunction G ℂ))
              (ρ : ClassFunction ↥T ℂ)
            * ClassFunction.inner (ClassFunction.restrict (H.subgroupOf T)
                (ρ : ClassFunction ↥T ℂ)) θ' :=
        Finset.single_le_sum hnn (Finset.mem_univ ψ)
    _ = ClassFunction.restrictionMultiplicity H (χ : ClassFunction G ℂ) θ :=
        (h1.trans h2).symm

omit [Fintype G] [Invertible (Nat.card G : ℂ)] in
open scoped ComplexOrder in
/-- **The θ-part lower bound, summed over a family**: for any finite set `S` of irreducible
characters of `T` (with `H ≤ T`), the multiplicity of `θ` in `Res_H χ` is at least
`∑_{ρ ∈ S} ⟨Res_T χ, ρ⟩ · ⟨Res_H ρ, θ⟩`.

Same expansion as `restrictionMultiplicity_mul_le_restrictionMultiplicity` (which is the
one-element case): `⟨Res_H χ, θ⟩ = ∑_ρ ⟨Res_T χ, ρ⟩·⟨Res ρ, θ'⟩` over **all** `ρ ∈ Irr(T)`,
a sum of products of non-negative integers, so dropping the terms outside `S` only decreases
it (`Finset.sum_le_sum_of_subset_of_nonneg`).  The two-element case is what separates two
distinct Clifford correspondents (`eq_of_induce_eq_induce_of_liesOver_of_inertia_eq`). -/
theorem sum_restrictionMultiplicity_mul_le_restrictionMultiplicity
    {H T : Subgroup G} (hHT : H ≤ T)
    [Fintype ↥T] [Invertible (Nat.card ↥T : ℂ)]
    [Fintype ↥(H.subgroupOf T)] [Invertible (Nat.card ↥(H.subgroupOf T) : ℂ)]
    [Fintype ↥H] [Invertible (Nat.card ↥H : ℂ)]
    (χ : IrreducibleCharacter G) (S : Finset (IrreducibleCharacter ↥T))
    {θ : ClassFunction ↥H ℂ} (hθ : IsIrreducibleCharacter θ) :
    ∑ ρ ∈ S,
        ClassFunction.restrictionMultiplicity T (χ : ClassFunction G ℂ) (ρ : ClassFunction ↥T ℂ)
          * ClassFunction.restrictionMultiplicity (H.subgroupOf T) (ρ : ClassFunction ↥T ℂ)
              (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hHT).toMonoidHom θ)
      ≤ ClassFunction.restrictionMultiplicity H (χ : ClassFunction G ℂ) θ := by
  classical
  haveI : Finite (IrreducibleCharacter ↥T) := finite_irreducibleCharacter (G := ↥T)
  letI : Fintype (IrreducibleCharacter ↥T) := Fintype.ofFinite _
  set θ' : ClassFunction ↥(H.subgroupOf T) ℂ :=
    ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hHT).toMonoidHom θ with hθ'
  have hθ'irr : IsIrreducibleCharacter θ' :=
    IsIrreducibleCharacter.compHom_of_surjective (Subgroup.subgroupOfEquivOfLe hHT).surjective hθ
  -- the H-level multiplicity, transported to `H.subgroupOf T`
  have h1 : ClassFunction.restrictionMultiplicity H (χ : ClassFunction G ℂ) θ
      = ClassFunction.inner (ClassFunction.restrict (H.subgroupOf T)
          (ClassFunction.restrict T (χ : ClassFunction G ℂ))) θ' := by
    rw [ClassFunction.restrict_subgroupOf_restrict hHT, hθ']
    exact (inner_compHom_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hHT)
      (ClassFunction.restrict H (χ : ClassFunction G ℂ)) θ).symm
  -- expand `Res_T χ` into irreducibles of `T` and push through
  have hres_sum : ∀ (s : Finset (IrreducibleCharacter ↥T))
      (F : IrreducibleCharacter ↥T → ClassFunction ↥T ℂ),
      ClassFunction.restrict (H.subgroupOf T) (∑ ρ ∈ s, F ρ)
        = ∑ ρ ∈ s, ClassFunction.restrict (H.subgroupOf T) (F ρ) := by
    intro s F
    induction s using Finset.induction_on with
    | empty =>
        ext y
        simp
    | insert a s ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha, ClassFunction.restrict_add, ih]
  have h2 : ClassFunction.inner (ClassFunction.restrict (H.subgroupOf T)
        (ClassFunction.restrict T (χ : ClassFunction G ℂ))) θ'
      = ∑ ρ : IrreducibleCharacter ↥T,
          ClassFunction.inner (ClassFunction.restrict T (χ : ClassFunction G ℂ))
              (ρ : ClassFunction ↥T ℂ)
            * ClassFunction.inner (ClassFunction.restrict (H.subgroupOf T)
                (ρ : ClassFunction ↥T ℂ)) θ' := by
    conv_lhs => rw [← sum_inner_irreducibleCharacter_smul (G := ↥T)
      (ClassFunction.restrict T (χ : ClassFunction G ℂ))]
    rw [hres_sum, inner_sum_left]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    rw [ClassFunction.restrict_smul, ClassFunction.inner_smul_left]
  -- every summand is a product of non-negative integers
  have hnn : ∀ ρ ∈ (Finset.univ : Finset (IrreducibleCharacter ↥T)), ρ ∉ S →
      (0 : ℂ) ≤ ClassFunction.inner (ClassFunction.restrict T (χ : ClassFunction G ℂ))
          (ρ : ClassFunction ↥T ℂ)
        * ClassFunction.inner (ClassFunction.restrict (H.subgroupOf T)
            (ρ : ClassFunction ↥T ℂ)) θ' := by
    intro ρ _ _
    refine mul_nonneg ?_ ?_
    · exact ClassFunction.restrictionMultiplicity_nonneg T χ.isIrreducible ρ.isIrreducible
    · exact ClassFunction.restrictionMultiplicity_nonneg (H.subgroupOf T) ρ.isIrreducible hθ'irr
  -- dropping the terms outside `S` only decreases the (non-negative) full sum
  calc ∑ ρ ∈ S,
        ClassFunction.restrictionMultiplicity T (χ : ClassFunction G ℂ) (ρ : ClassFunction ↥T ℂ)
          * ClassFunction.restrictionMultiplicity (H.subgroupOf T) (ρ : ClassFunction ↥T ℂ) θ'
      ≤ ∑ ρ : IrreducibleCharacter ↥T,
          ClassFunction.inner (ClassFunction.restrict T (χ : ClassFunction G ℂ))
              (ρ : ClassFunction ↥T ℂ)
            * ClassFunction.inner (ClassFunction.restrict (H.subgroupOf T)
                (ρ : ClassFunction ↥T ℂ)) θ' :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S) hnn
    _ = ClassFunction.restrictionMultiplicity H (χ : ClassFunction G ℂ) θ :=
        (h1.trans h2).symm

open scoped ComplexOrder in
/-- **The Clifford correspondence, irreducibility half** (Isaacs, *Character Theory*,
Theorem 6.11; issue 9002 (G3)).  Let `H ⊴ G` and let `θ ∈ Irr(H)` have inertia group
exactly `T` (so `H ≤ T`), and let `ψ ∈ Irr(T)` lie over `θ` (transported along
`↥(H.subgroupOf T) ≃* ↥H`).  Then `Ind_T^G ψ` is **irreducible**.

θ-part counting (no Mackey formula): any irreducible constituent `χ` of `Ind_T^G ψ` with
multiplicity `m ≥ 1` satisfies `⟨Res_H χ, θ⟩ ≥ m·e` for `e = ⟨Res ψ, θ'⟩`
(`restrictionMultiplicity_mul_le_restrictionMultiplicity`), so by the single-orbit degree
formulas at `(G, H)` and `(T, H.subgroupOf T)`,
`χ(1) = ⟨Res_H χ, θ⟩·[G:T]·θ(1) ≥ m·[G:T]·ψ(1)`; against `χ(1) ≤ (Ind ψ)(1) = [G:T]·ψ(1)`
this forces `m = 1` with equal degrees, and `Ind ψ = χ` by degree exhaustion
(`induce_eq_coe_of_inner_eq_one_of_apply_one_eq`).

Combined with the extension theorem (Isaacs 8.16, `CanonicalCharacterExtension`) and the
Gallagher decomposition (`GallagherDecomposition`) this completes the constructive Clifford
decomposition of `Ind_H^G θ` for an abelian coprime inertia quotient (Peterfalvi
(1.7)(b)). -/
theorem isIrreducibleCharacter_induce_of_liesOver_of_inertia_eq
    {H T : Subgroup G} [H.Normal] [(H.subgroupOf T).Normal] (hHT : H ≤ T)
    [Invertible (Nat.card ↥T : ℂ)]
    [Fintype ↥(H.subgroupOf T)] [Invertible (Nat.card ↥(H.subgroupOf T) : ℂ)]
    {θ : ClassFunction ↥H ℂ} (hθ : IsIrreducibleCharacter θ)
    (hinertia : ClassFunction.inertia (G := G) θ = T)
    (ψ : IrreducibleCharacter ↥T)
    (hover : ClassFunction.restrictionMultiplicity (H.subgroupOf T)
        (ψ : ClassFunction ↥T ℂ)
        (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hHT).toMonoidHom θ) ≠ 0) :
    IsIrreducibleCharacter (ClassFunction.induce T (ψ : ClassFunction ↥T ℂ)) := by
  classical
  letI : Fintype ↥T := Fintype.ofFinite _
  letI : Fintype ↥H := Fintype.ofFinite _
  letI : Invertible (Nat.card ↥H : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  haveI : Finite (IrreducibleCharacter G) := finite_irreducibleCharacter (G := G)
  letI : Fintype (IrreducibleCharacter G) := Fintype.ofFinite _
  haveI : Finite (IrreducibleCharacter ↥H) := finite_irreducibleCharacter (G := ↥H)
  letI : Fintype (IrreducibleCharacter ↥H) := Fintype.ofFinite _
  haveI : Finite (IrreducibleCharacter ↥(H.subgroupOf T)) :=
    finite_irreducibleCharacter (G := ↥(H.subgroupOf T))
  letI : Fintype (IrreducibleCharacter ↥(H.subgroupOf T)) := Fintype.ofFinite _
  -- bundled forms, with definitional coercion bridges
  set θb : IrreducibleCharacter ↥H := ⟨θ, hθ⟩ with hθb
  have hθ'irr : IsIrreducibleCharacter (ClassFunction.compHom
      (Subgroup.subgroupOfEquivOfLe hHT).toMonoidHom θ) :=
    IsIrreducibleCharacter.compHom_of_surjective
      (Subgroup.subgroupOfEquivOfLe hHT).surjective hθ
  set θ'b : IrreducibleCharacter ↥(H.subgroupOf T) :=
    ⟨ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hHT).toMonoidHom θ, hθ'irr⟩
    with hθ'b
  have hcoeθ : (θb : ClassFunction ↥H ℂ) = θ := rfl
  have hcoeθ' : (θ'b : ClassFunction ↥(H.subgroupOf T) ℂ)
      = ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hHT).toMonoidHom θ := rfl
  -- the ℕ-valued degrees and multiplicities
  obtain ⟨dθ, hdθpos, hdθ⟩ := irreducibleCharacter_apply_one_eq_pos_natCast θb
  rw [hcoeθ] at hdθ
  obtain ⟨dψ, hdψpos, hdψ⟩ := irreducibleCharacter_apply_one_eq_pos_natCast ψ
  obtain ⟨eψ, heψ⟩ :=
    IrreducibleCharacter.restrictionMultiplicity_natCast (H := H.subgroupOf T) ψ θ'b
  rw [hcoeθ'] at heψ
  have heψ1 : 1 ≤ eψ := by
    rcases Nat.eq_zero_or_pos eψ with h | h
    · exact absurd (by rw [heψ, h, Nat.cast_zero]) hover
    · exact h
  -- Step 1: `ψ(1) = eψ·θ(1)`, since `θ'` has full inertia in `T`
  have hoverψ : IrreducibleCharacter.LiesOver (H := H.subgroupOf T) ψ θ'b := by
    change ClassFunction.restrictionMultiplicity (H.subgroupOf T) (ψ : ClassFunction ↥T ℂ)
        (θ'b : ClassFunction ↥(H.subgroupOf T) ℂ) ≠ 0
    rw [hcoeθ']
    exact hover
  have hstep1 := apply_one_eq_restrictionMultiplicity_mul_index_inertia
    (G := ↥T) (H := H.subgroupOf T) ψ θ'b hoverψ
  have hinvT : ∀ t : ↥T, ClassFunction.conjBy ((t : G)) θ = θ := fun t => by
    have hmem : (t : G) ∈ ClassFunction.inertia (G := G) θ := by
      rw [hinertia]
      exact t.2
    exact (ClassFunction.mem_inertia).mp hmem
  have hinertia' : IrreducibleCharacter.inertia (G := ↥T) (H := H.subgroupOf T) θ'b = ⊤ :=
    inertia_compHom_subgroupOfEquivOfLe_eq_top hHT hinvT
  rw [hcoeθ', hinertia', Subgroup.index_top, Nat.cast_one, mul_one, heψ,
    ClassFunction.compHom_apply, map_one, hdθ, hdψ] at hstep1
  have hstep1N : dψ = eψ * dθ := by exact_mod_cast hstep1
  -- some irreducible constituent `χ` of `Ind_T^G ψ` exists
  have hEx : ∃ χ : IrreducibleCharacter G,
      ClassFunction.restrictionMultiplicity T (χ : ClassFunction G ℂ)
        (ψ : ClassFunction ↥T ℂ) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hzero : ClassFunction.induce T (ψ : ClassFunction ↥T ℂ) = 0 := by
      rw [induce_eq_sum_inner_restrict_smul (N := T) (ψ : ClassFunction ↥T ℂ)]
      refine Finset.sum_eq_zero fun η _ => ?_
      have h0 : ClassFunction.inner (ψ : ClassFunction ↥T ℂ)
          (ClassFunction.restrict T (η : ClassFunction G ℂ)) = 0 := by
        rw [inner_conj_symm (ClassFunction.restrict T (η : ClassFunction G ℂ))
            (ψ : ClassFunction ↥T ℂ),
          ← ClassFunction.restrictionMultiplicity_def, hcon η, star_zero]
      rw [h0, zero_smul]
    have hdeg1 := ClassFunction.induce_apply_one T (ψ : ClassFunction ↥T ℂ)
    rw [hzero, hdψ] at hdeg1
    have h00 : ((0 : ClassFunction G ℂ)) (1 : G) = 0 := rfl
    rw [h00] at hdeg1
    have hTne : T.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    exact (mul_ne_zero (Nat.cast_ne_zero.mpr hTne)
      (Nat.cast_ne_zero.mpr hdψpos.ne' : ((dψ : ℕ) : ℂ) ≠ 0)) hdeg1.symm
  obtain ⟨χ, hmne⟩ := hEx
  obtain ⟨m, hm⟩ := IrreducibleCharacter.restrictionMultiplicity_natCast (H := T) χ ψ
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · exact absurd (by rw [hm, h, Nat.cast_zero]) hmne
    · exact h
  obtain ⟨eχ, heχ⟩ := IrreducibleCharacter.restrictionMultiplicity_natCast (H := H) χ θb
  rw [hcoeθ] at heχ
  -- the θ-part lower bound `m·eψ ≤ eχ`
  have hlow := restrictionMultiplicity_mul_le_restrictionMultiplicity (G := G) hHT χ ψ hθ
  rw [hm, heψ, heχ] at hlow
  have hlowN : m * eψ ≤ eχ := by exact_mod_cast hlow
  have heχ1 : 1 ≤ eχ := le_trans (Nat.mul_pos hm1 heψ1) hlowN
  -- the (G, H) degree formula: `χ(1) = eχ·[G:T]·θ(1)`
  have hoverχ : IrreducibleCharacter.LiesOver (H := H) χ θb := by
    change ClassFunction.restrictionMultiplicity H (χ : ClassFunction G ℂ)
        (θb : ClassFunction ↥H ℂ) ≠ 0
    rw [hcoeθ, heχ]
    exact Nat.cast_ne_zero.mpr (Nat.one_le_iff_ne_zero.mp heχ1)
  have hdegχ := apply_one_eq_restrictionMultiplicity_mul_index_inertia
    (G := G) (H := H) χ θb hoverχ
  have hinertiaχ : IrreducibleCharacter.inertia (G := G) (H := H) θb = T := hinertia
  obtain ⟨dχ, hdχpos, hdχ⟩ := irreducibleCharacter_apply_one_eq_pos_natCast χ
  rw [hcoeθ, hinertiaχ, heχ, hdθ, hdχ] at hdegχ
  have hdegχN : dχ = eχ * T.index * dθ := by exact_mod_cast hdegχ
  -- the constituent degree bound: `χ(1) ≤ (Ind ψ)(1) = [G:T]·ψ(1)`
  have hoverχψ : IrreducibleCharacter.LiesOver (H := T) χ ψ := hmne
  have hupper := apply_one_le_induce_apply_one_of_liesOver (I := T) χ ψ hoverχψ
  rw [ClassFunction.induce_apply_one, hdχ, hdψ] at hupper
  have hupperN : dχ ≤ T.index * dψ := by exact_mod_cast hupper
  -- the squeeze: `m = 1` and the degrees agree
  have hTpos : 0 < T.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have heχeψ : eχ ≤ eψ := by
    have h2 : eχ * (T.index * dθ) ≤ eψ * (T.index * dθ) := by
      calc eχ * (T.index * dθ) = eχ * T.index * dθ := by ring
        _ = dχ := hdegχN.symm
        _ ≤ T.index * dψ := hupperN
        _ = T.index * (eψ * dθ) := by rw [hstep1N]
        _ = eψ * (T.index * dθ) := by ring
    exact Nat.le_of_mul_le_mul_right h2 (Nat.mul_pos hTpos hdθpos)
  have hmeq : m = 1 := by
    have h1 : m * eψ ≤ 1 * eψ := by
      rw [one_mul]
      exact le_trans hlowN heχeψ
    have h2 : m ≤ 1 := Nat.le_of_mul_le_mul_right h1 heψ1
    omega
  have hdeqN : dχ = T.index * dψ := by
    have h1 : eψ ≤ eχ := by
      have h0 := hlowN
      rw [hmeq, one_mul] at h0
      exact h0
    rw [hdegχN, Nat.le_antisymm heχeψ h1, hstep1N]
    ring
  -- conclude by degree exhaustion
  have h1 : ClassFunction.inner (ClassFunction.induce T (ψ : ClassFunction ↥T ℂ))
      (χ : ClassFunction G ℂ) = 1 := by
    rw [inner_induce_coe_eq_restrictionMultiplicity, hm, hmeq, Nat.cast_one]
  have hdeg : ClassFunction.induce T (ψ : ClassFunction ↥T ℂ) (1 : G)
      = (χ : ClassFunction G ℂ) (1 : G) := by
    rw [ClassFunction.induce_apply_one, hdψ, hdχ, ← Nat.cast_mul, ← hdeqN]
  have hfinal := induce_eq_coe_of_inner_eq_one_of_apply_one_eq ψ χ h1 hdeg
  rw [hfinal]
  exact χ.isIrreducible

open scoped ComplexOrder in
/-- **Peterfalvi (1.7.a), distinctness half** (the injectivity of the Clifford correspondence,
[Is] *Character Theory*, Theorem 6.11).  Let `H ⊴ G` and let `θ ∈ Irr(H)` have inertia group
exactly `T`.  If `ψ, ψ' ∈ Irr(T)` both lie over `θ` and `Ind_T^G ψ = Ind_T^G ψ'`, then
`ψ = ψ'`.  In the book's notation: the characters `χᵢ = Ind_T^G ψᵢ` attached to the distinct
constituents `ψᵢ` of `Ind_H^T θ` are pairwise **distinct**.

θ-part counting, as in the irreducibility half.  Write `χ = Ind_T^G ψ = Ind_T^G ψ'`,
irreducible by `isIrreducibleCharacter_induce_of_liesOver_of_inertia_eq`.  Frobenius
reciprocity gives `⟨Res_T χ, ψ⟩ = ⟨χ, χ⟩ = 1 = ⟨Res_T χ, ψ'⟩`, so the two-element case of
`sum_restrictionMultiplicity_mul_le_restrictionMultiplicity` bounds `⟨Res_H χ, θ⟩ ≥ e + e'`,
where `e = ⟨Res_H ψ, θ⟩ ≥ 1` and `e' = ⟨Res_H ψ', θ⟩ ≥ 1`.  But the two Clifford degree
formulas `χ(1) = ⟨Res_H χ, θ⟩·[G:T]·θ(1)` (at `(G, H)`, using `I_G(θ) = T`) and
`χ(1) = [G:T]·ψ(1) = [G:T]·e·θ(1)` (at `(T, H)`, where `θ` is invariant) force
`⟨Res_H χ, θ⟩ = e`, whence `e' = 0` — contradicting that `ψ'` lies over `θ`. -/
theorem eq_of_induce_eq_induce_of_liesOver_of_inertia_eq
    {H T : Subgroup G} [H.Normal] [(H.subgroupOf T).Normal] (hHT : H ≤ T)
    [Invertible (Nat.card ↥T : ℂ)]
    [Fintype ↥(H.subgroupOf T)] [Invertible (Nat.card ↥(H.subgroupOf T) : ℂ)]
    {θ : ClassFunction ↥H ℂ} (hθ : IsIrreducibleCharacter θ)
    (hinertia : ClassFunction.inertia (G := G) θ = T)
    (ψ ψ' : IrreducibleCharacter ↥T)
    (hover : ClassFunction.restrictionMultiplicity (H.subgroupOf T)
        (ψ : ClassFunction ↥T ℂ)
        (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hHT).toMonoidHom θ) ≠ 0)
    (hover' : ClassFunction.restrictionMultiplicity (H.subgroupOf T)
        (ψ' : ClassFunction ↥T ℂ)
        (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hHT).toMonoidHom θ) ≠ 0)
    (heq : ClassFunction.induce T (ψ : ClassFunction ↥T ℂ)
        = ClassFunction.induce T (ψ' : ClassFunction ↥T ℂ)) :
    ψ = ψ' := by
  classical
  by_contra hne
  letI : Fintype ↥T := Fintype.ofFinite _
  letI : Fintype ↥H := Fintype.ofFinite _
  letI : Invertible (Nat.card ↥H : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  haveI : Finite (IrreducibleCharacter ↥H) := finite_irreducibleCharacter (G := ↥H)
  haveI : Finite (IrreducibleCharacter ↥(H.subgroupOf T)) :=
    finite_irreducibleCharacter (G := ↥(H.subgroupOf T))
  -- bundled forms, with definitional coercion bridges
  set θb : IrreducibleCharacter ↥H := ⟨θ, hθ⟩ with hθb
  have hθ'irr : IsIrreducibleCharacter (ClassFunction.compHom
      (Subgroup.subgroupOfEquivOfLe hHT).toMonoidHom θ) :=
    IsIrreducibleCharacter.compHom_of_surjective
      (Subgroup.subgroupOfEquivOfLe hHT).surjective hθ
  set θ'b : IrreducibleCharacter ↥(H.subgroupOf T) :=
    ⟨ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hHT).toMonoidHom θ, hθ'irr⟩
    with hθ'b
  have hcoeθ : (θb : ClassFunction ↥H ℂ) = θ := rfl
  have hcoeθ' : (θ'b : ClassFunction ↥(H.subgroupOf T) ℂ)
      = ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hHT).toMonoidHom θ := rfl
  -- `χ = Ind_T^G ψ` is irreducible (the correspondence's irreducibility half)
  have hirr : IsIrreducibleCharacter (ClassFunction.induce T (ψ : ClassFunction ↥T ℂ)) :=
    isIrreducibleCharacter_induce_of_liesOver_of_inertia_eq hHT hθ hinertia ψ hover
  obtain ⟨χ, hχ⟩ : ∃ χ : IrreducibleCharacter G,
      (χ : ClassFunction G ℂ) = ClassFunction.induce T (ψ : ClassFunction ↥T ℂ) :=
    ⟨⟨_, hirr⟩, rfl⟩
  -- both `ψ` and `ψ'` occur in `Res_T χ` with multiplicity one
  have hself : ClassFunction.inner (χ : ClassFunction G ℂ) (χ : ClassFunction G ℂ) = 1 := by
    classical simpa using irreducibleCharacter_inner_eq_ite χ χ
  have hinner : ClassFunction.inner (ClassFunction.induce T (ψ : ClassFunction ↥T ℂ))
      (χ : ClassFunction G ℂ) = 1 := by
    rw [← hχ]; exact hself
  have hinner' : ClassFunction.inner (ClassFunction.induce T (ψ' : ClassFunction ↥T ℂ))
      (χ : ClassFunction G ℂ) = 1 := by
    rw [← heq, ← hχ]; exact hself
  have hmψ : ClassFunction.restrictionMultiplicity T (χ : ClassFunction G ℂ)
      (ψ : ClassFunction ↥T ℂ) = 1 := by
    rw [← inner_induce_coe_eq_restrictionMultiplicity ψ χ]; exact hinner
  have hmψ' : ClassFunction.restrictionMultiplicity T (χ : ClassFunction G ℂ)
      (ψ' : ClassFunction ↥T ℂ) = 1 := by
    rw [← inner_induce_coe_eq_restrictionMultiplicity ψ' χ]; exact hinner'
  -- the two-element θ-part bound `e + e' ≤ ⟨Res_H χ, θ⟩`
  have hpair := sum_restrictionMultiplicity_mul_le_restrictionMultiplicity (G := G) hHT χ
    ({ψ, ψ'} : Finset (IrreducibleCharacter ↥T)) hθ
  rw [Finset.sum_pair hne, hmψ, hmψ', one_mul, one_mul] at hpair
  -- pass to the natural-number degrees and multiplicities
  obtain ⟨dθ, hdθpos, hdθ⟩ := irreducibleCharacter_apply_one_eq_pos_natCast θb
  rw [hcoeθ] at hdθ
  obtain ⟨dψ, hdψpos, hdψ⟩ := irreducibleCharacter_apply_one_eq_pos_natCast ψ
  obtain ⟨eψ, heψ⟩ := IrreducibleCharacter.restrictionMultiplicity_natCast
    (H := H.subgroupOf T) ψ θ'b
  rw [hcoeθ'] at heψ
  obtain ⟨eψ', heψ'⟩ := IrreducibleCharacter.restrictionMultiplicity_natCast
    (H := H.subgroupOf T) ψ' θ'b
  rw [hcoeθ'] at heψ'
  obtain ⟨eχ, heχ⟩ := IrreducibleCharacter.restrictionMultiplicity_natCast (H := H) χ θb
  rw [hcoeθ] at heχ
  rw [heψ, heψ', heχ] at hpair
  have hpairN : eψ + eψ' ≤ eχ := by exact_mod_cast hpair
  have heψ1 : 1 ≤ eψ := by
    rcases Nat.eq_zero_or_pos eψ with h | h
    · exact absurd (by rw [heψ, h, Nat.cast_zero]) hover
    · exact h
  have heψ'1 : 1 ≤ eψ' := by
    rcases Nat.eq_zero_or_pos eψ' with h | h
    · exact absurd (by rw [heψ', h, Nat.cast_zero]) hover'
    · exact h
  -- `ψ(1) = eψ·θ(1)`, since `θ'` is `T`-invariant (`T = I_G(θ)`)
  have hoverψ : IrreducibleCharacter.LiesOver (H := H.subgroupOf T) ψ θ'b := by
    change ClassFunction.restrictionMultiplicity (H.subgroupOf T) (ψ : ClassFunction ↥T ℂ)
        (θ'b : ClassFunction ↥(H.subgroupOf T) ℂ) ≠ 0
    rw [hcoeθ']; exact hover
  have hstep1 := apply_one_eq_restrictionMultiplicity_mul_index_inertia
    (G := ↥T) (H := H.subgroupOf T) ψ θ'b hoverψ
  have hinvT : ∀ t : ↥T, ClassFunction.conjBy ((t : G)) θ = θ := fun t => by
    have hmem : (t : G) ∈ ClassFunction.inertia (G := G) θ := by
      rw [hinertia]; exact t.2
    exact (ClassFunction.mem_inertia).mp hmem
  have hinertia' : IrreducibleCharacter.inertia (G := ↥T) (H := H.subgroupOf T) θ'b = ⊤ :=
    inertia_compHom_subgroupOfEquivOfLe_eq_top hHT hinvT
  rw [hcoeθ', hinertia', Subgroup.index_top, Nat.cast_one, mul_one, heψ,
    ClassFunction.compHom_apply, map_one, hdθ, hdψ] at hstep1
  have hstep1N : dψ = eψ * dθ := by exact_mod_cast hstep1
  -- `χ(1) = eχ·[G:T]·θ(1)` (Clifford at `(G, H)`) and `χ(1) = [G:T]·ψ(1)` (degree of `Ind`)
  have hoverχ : IrreducibleCharacter.LiesOver (H := H) χ θb := by
    change ClassFunction.restrictionMultiplicity H (χ : ClassFunction G ℂ)
        (θb : ClassFunction ↥H ℂ) ≠ 0
    rw [hcoeθ, heχ]
    exact Nat.cast_ne_zero.mpr (by omega)
  have hdegχ := apply_one_eq_restrictionMultiplicity_mul_index_inertia
    (G := G) (H := H) χ θb hoverχ
  have hinertiaχ : IrreducibleCharacter.inertia (G := G) (H := H) θb = T := hinertia
  obtain ⟨dχ, hdχpos, hdχ⟩ := irreducibleCharacter_apply_one_eq_pos_natCast χ
  rw [hcoeθ, hinertiaχ, heχ, hdθ, hdχ] at hdegχ
  have hdegχN : dχ = eχ * T.index * dθ := by exact_mod_cast hdegχ
  have hdegind : dχ = T.index * dψ := by
    have h : (χ : ClassFunction G ℂ) (1 : G)
        = ClassFunction.induce T (ψ : ClassFunction ↥T ℂ) (1 : G) := by rw [hχ]
    rw [hdχ, ClassFunction.induce_apply_one, hdψ] at h
    exact_mod_cast h
  -- the two formulas force `eχ = eψ`, so `eψ' = 0` — contradicting `hover'`
  have hTpos : 0 < T.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hcancel : eχ * (T.index * dθ) = eψ * (T.index * dθ) := by
    calc eχ * (T.index * dθ) = eχ * T.index * dθ := by ring
      _ = dχ := hdegχN.symm
      _ = T.index * dψ := hdegind
      _ = T.index * (eψ * dθ) := by rw [hstep1N]
      _ = eψ * (T.index * dθ) := by ring
  have heχeψ : eχ = eψ :=
    Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hTpos hdθpos) hcancel
  omega

open scoped ComplexOrder in
/-- **Peterfalvi (1.7.a)**.  Let `H ⊴ G`, let `θ ∈ Irr(H)` have inertia group `T = I_G(θ)`,
and write `Ind_H^T θ = ∑_{i=1}^n eᵢ ψᵢ` with the `ψᵢ` distinct elements of `Irr(T)`.  Put
`χᵢ = Ind_T^G ψᵢ`.  Then the `χᵢ` are irreducible characters of `G`, they are pairwise
distinct, and `Ind_H^G θ = ∑_{i=1}^n eᵢ χᵢ`.

The book cites [Is] Theorem 6.11 for the whole statement.  Here the three clauses are
`isIrreducibleCharacter_induce_of_liesOver_of_inertia_eq` (irreducibility),
`eq_of_induce_eq_induce_of_liesOver_of_inertia_eq` (distinctness), and induction in stages
(`induce_induce_subgroupOf`) together with the linearity of induction (`ClassFunction.induce_sum`,
`ClassFunction.induce_smul`) for the decomposition.  As in the book, the decomposition
`Ind_H^T θ = ∑ eᵢ ψᵢ` is a hypothesis on a finite family `S = {ψ₁, …, ψₙ} ⊆ Irr(T)`; that each
`ψᵢ` lies over `θ` — automatic for the constituents of `Ind_H^T θ` — is what makes the Clifford
correspondence apply, and the coefficients `eᵢ` are unrestricted (no coprimality, and `T/H` need
not be abelian). -/
theorem induce_eq_sum_smul_induce_of_inertia_eq
    {H T : Subgroup G} [H.Normal] [(H.subgroupOf T).Normal] (hHT : H ≤ T)
    [Invertible (Nat.card ↥H : ℂ)] [Fintype ↥T] [Invertible (Nat.card ↥T : ℂ)]
    [Fintype ↥(H.subgroupOf T)] [Invertible (Nat.card ↥(H.subgroupOf T) : ℂ)]
    {θ : ClassFunction ↥H ℂ} (hθ : IsIrreducibleCharacter θ)
    (hinertia : ClassFunction.inertia (G := G) θ = T)
    (S : Finset (IrreducibleCharacter ↥T)) (e : IrreducibleCharacter ↥T → ℂ)
    (hover : ∀ ψ ∈ S, ClassFunction.restrictionMultiplicity (H.subgroupOf T)
        (ψ : ClassFunction ↥T ℂ)
        (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hHT).toMonoidHom θ) ≠ 0)
    (hdecomp : ClassFunction.induce (H.subgroupOf T)
          (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hHT).toMonoidHom θ)
        = ∑ ψ ∈ S, e ψ • (ψ : ClassFunction ↥T ℂ)) :
    (∀ ψ ∈ S, IsIrreducibleCharacter (ClassFunction.induce T (ψ : ClassFunction ↥T ℂ)))
      ∧ (∀ ψ ∈ S, ∀ ψ' ∈ S, ClassFunction.induce T (ψ : ClassFunction ↥T ℂ)
            = ClassFunction.induce T (ψ' : ClassFunction ↥T ℂ) → ψ = ψ')
      ∧ ClassFunction.induce H θ
          = ∑ ψ ∈ S, e ψ • ClassFunction.induce T (ψ : ClassFunction ↥T ℂ) := by
  refine ⟨fun ψ hψ =>
      isIrreducibleCharacter_induce_of_liesOver_of_inertia_eq hHT hθ hinertia ψ (hover ψ hψ),
    fun ψ hψ ψ' hψ' hind => eq_of_induce_eq_induce_of_liesOver_of_inertia_eq hHT hθ hinertia
      ψ ψ' (hover ψ hψ) (hover ψ' hψ') hind, ?_⟩
  rw [← induce_induce_subgroupOf (M := G) hHT θ, hdecomp, ClassFunction.induce_sum]
  exact Finset.sum_congr rfl fun ψ _ => ClassFunction.induce_smul T (e ψ) _

end OddOrder.RepresentationTheory
