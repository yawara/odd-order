/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.CliffordConjugateChar
import OddOrder.GroupTheory.RepresentationTheory.Clifford
import OddOrder.GroupTheory.RepresentationTheory.InducedIrreducible

/-!
# Clifford's theorem: the constituents of a restriction form a single conjugation orbit

`OddOrder.GroupTheory.RepresentationTheory` shared module: the **single-orbit** half of Clifford's
theorem ([Isaacs] Thm 6.5), the input that lets `clifford_decomposition` become a genuine theorem and
that the (9.9.a) Clifford-degree assembly (`apply_one_eq_sum_restrictionMultiplicity_mul`) needs.

For a `G`-irreducible representation `ρ` and a normal subgroup `H ⊴ G`, any two simple `k[H]`-
submodules of the restriction `Res^G_H ρ` are `G`-conjugate (their `G`-conjugates span `⊤`, so each
is isomorphic to a conjugate of the other, `iSup_map_conjSemilinearEnd_eq_top`).  At the level of
characters this says their characters lie in one orbit of the conjugation action `h ↦ g⁻¹ h g`.

## Main statements

* `character_conj_of_simpleSubmodule` — for two simple `k[H]`-submodules `N`, `N'` of `Res^G_H ρ`
  (`ρ` irreducible), there is `g : G` with `χ_{N'}(h) = χ_N(g⁻¹ h g)`: the constituent characters
  form a single conjugation orbit (module-level Clifford single-orbit).
-/

namespace OddOrder.RepresentationTheory

open Representation
open scoped MonoidAlgebra

variable {G : Type*} [Group G]
variable {k : Type*} [Field k]
variable {V : Type*} [AddCommGroup V] [Module k V]
variable (ρ : Representation k G V)

set_option backward.isDefEq.respectTransparency false in
/-- **Clifford single-orbit, module level.**  For a `G`-irreducible representation `ρ` and a normal
subgroup `H ⊴ G`, any two simple `k[H]`-submodules `N`, `N'` of the restriction `Res^G_H ρ` have
conjugate characters: there is `g : G` with `χ_{N'}(h) = χ_N(g⁻¹ h g)` for all `h ∈ H`.

Proof: the `G`-conjugates `N.map (conjSemilinearEnd ρ g)` span `⊤`
(`iSup_map_conjSemilinearEnd_eq_top`, irreducibility of `ρ`), so the simple submodule `N'` is
`k[H]`-isomorphic to one of them, `N.map (conjSemilinearEnd ρ g)`
(`Submodule.linearEquiv_of_sSup_eq_top`).  Transporting that isomorphism to the subrepresentations
(`equivOfAsModuleEquiv`) and applying `Representation.char_iso` equates `χ_{N'}` with the character
of the conjugate; `character_subRep_conj` rewrites the latter as `χ_N(g⁻¹ · g)`. -/
theorem character_conj_of_simpleSubmodule [ρ.IsIrreducible] [FiniteDimensional k V]
    {H : Subgroup G} [hH : H.Normal]
    (N N' : Submodule k[↥H] (resRep ρ H).asModule) (hN : N ≠ ⊥)
    [IsSimpleModule k[↥H] ↥N] [IsSimpleModule k[↥H] ↥N'] :
    ∃ g : G, ((Subrepresentation.ofSubmodule' N').toRepresentation).character
      = fun h => ((Subrepresentation.ofSubmodule' N).toRepresentation).character
          (conjNormalMulAut H g⁻¹ h) := by
  classical
  haveI : ∀ S : (Set.range fun g : G => N.map (conjSemilinearEnd (H := H) ρ g)),
      IsSimpleModule k[↥H] (S : Submodule k[↥H] (resRep ρ H).asModule) := by
    rintro ⟨_, g, rfl⟩
    exact isSimpleModule_map_conjSemilinearEnd ρ g N
  obtain ⟨S, hS, ⟨e⟩⟩ := Submodule.linearEquiv_of_sSup_eq_top N'
    (Set.range fun g : G => N.map (conjSemilinearEnd (H := H) ρ g))
    (by rw [sSup_range]; exact iSup_map_conjSemilinearEnd_eq_top ρ N hN)
  obtain ⟨g, rfl⟩ := hS
  refine ⟨g, ?_⟩
  have hcharEq : ((Subrepresentation.ofSubmodule' N').toRepresentation).character
      = ((Subrepresentation.ofSubmodule'
          (N.map (conjSemilinearEnd (H := H) ρ g))).toRepresentation).character :=
    Representation.char_iso
      (equivOfAsModuleEquiv
        ((subRepAsModuleEquiv (resRep ρ H) N').symm.trans
          (e.trans (subRepAsModuleEquiv (resRep ρ H)
            (N.map (conjSemilinearEnd (H := H) ρ g))))))
  rw [hcharEq]
  funext h
  exact character_subRep_conj ρ N g h

set_option backward.isDefEq.respectTransparency false in
/-- **A nonzero intertwiner yields a simple constituent submodule** (the module side of the
constituent ⟺ submodule bridge).  If `σ` is an irreducible `k[H]`-representation and there is a
nonzero `H`-equivariant map `f : σ → Res^G_H ρ`, then `Res^G_H ρ` has a simple `k[H]`-submodule `N`
whose subrepresentation character equals `χ_σ`.  Proof: pass `f` to its `k[H]`-linear `asModule`
form (`equivLinearMapAsModule`); it is nonzero, so injective by Schur
(`LinearMap.injective_of_ne_zero`, `σ.asModule` simple); its range is a simple submodule
`k[H]`-isomorphic to `σ.asModule` (`LinearEquiv.ofInjective`), and transporting that isomorphism
through `equivOfAsModuleEquiv` + `char_iso` equates the characters. -/
theorem exists_simpleSubmodule_character_eq_of_ne_zero_intertwiner [FiniteDimensional k V]
    {H : Subgroup G} [hH : H.Normal]
    {W : Type*} [AddCommGroup W] [Module k W]
    (σ : Representation k ↥H W) [σ.IsIrreducible]
    {f : Representation.IntertwiningMap σ (resRep ρ H)} (hf : f ≠ 0) :
    ∃ N : Submodule k[↥H] (resRep ρ H).asModule, IsSimpleModule k[↥H] ↥N ∧
      ((Subrepresentation.ofSubmodule' N).toRepresentation).character = σ.character := by
  haveI : IsSimpleModule k[↥H] σ.asModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule σ).mp inferInstance
  set fam := Representation.IntertwiningMap.equivLinearMapAsModule σ (resRep ρ H) f with hfam
  have hfam_ne : fam ≠ 0 := by
    rw [hfam, ne_eq, LinearEquiv.map_eq_zero_iff]; exact hf
  have hinj : Function.Injective fam := LinearMap.injective_of_ne_zero hfam_ne
  refine ⟨LinearMap.range fam, ?_, ?_⟩
  · exact (LinearEquiv.ofInjective fam hinj).isSimpleModule_iff.mp inferInstance
  · refine Representation.char_iso
      (equivOfAsModuleEquiv
        ((subRepAsModuleEquiv (resRep ρ H) (LinearMap.range fam)).symm.trans
          (LinearEquiv.ofInjective fam hinj).symm))

set_option backward.isDefEq.respectTransparency false in
/-- **Clifford's theorem, single-orbit (character level)** ([Isaacs] Thm 6.5, first clause): for a
`G`-irreducible character `χ` and a normal subgroup `H ⊴ G`, the irreducible constituents of
`Res^G_H χ` form a single `G`-conjugation orbit.  This discharges the
`RestrictionConstituentsSingleOrbit` hypothesis that `clifford_decomposition` was parametrized on,
and is the input the (9.9.a) Clifford-degree assembly needs (with
`hasCommonRestrictionMultiplicity_of_singleOrbit`).

Proof: realize `χ` by a `G`-irreducible `ρ`.  A constituent `ψ` of `Res χ` has nonzero restriction
multiplicity, hence (`restrictionMultiplicity_eq_finrank_intertwiningMap`) a nonzero `H`-intertwiner
`σ_ψ → Res ρ`, which (`exists_simpleSubmodule_character_eq_of_ne_zero_intertwiner`) yields a simple
`k[H]`-submodule `N_ψ` of `Res ρ` with `χ_{N_ψ} = ψ`.  For two constituents `θ`, `η` the submodules
`N_θ`, `N_η` are `G`-conjugate (`character_conj_of_simpleSubmodule`), giving `g` with
`θ(h) = η(g⁻¹ h g)`, i.e. `conjBy g θ = η`. -/
theorem restrictionConstituentsSingleOrbit_of_isIrreducible
    {H : Subgroup G} [hH : H.Normal] [Fintype ↥H] [Invertible (Nat.card ↥H : ℂ)]
    (χ : IrreducibleCharacter G) :
    IrreducibleCharacter.RestrictionConstituentsSingleOrbit (G := G) (H := H) χ := by
  classical
  obtain ⟨V, _, _, _, ρ, hρirr, hρchar⟩ := χ.isIrreducible
  haveI := hρirr
  -- Every constituent `ψ` of `Res χ` is the character of a simple `k[H]`-submodule of `Res ρ`.
  have wrapper : ∀ ψ : IrreducibleCharacter ↥H, IrreducibleCharacter.LiesOver (G := G) (H := H) χ ψ →
      ∃ N : Submodule ℂ[↥H] (resRep ρ H).asModule, IsSimpleModule ℂ[↥H] ↥N ∧
        ((Subrepresentation.ofSubmodule' N).toRepresentation).character
          = (ψ : ClassFunction ↥H ℂ) := by
    intro ψ hψ
    obtain ⟨W, _, _, _, σ, hσirr, hσchar⟩ := ψ.isIrreducible
    haveI := hσirr
    have hfr := ClassFunction.restrictionMultiplicity_eq_finrank_intertwiningMap (H := H) ρ σ hρchar hσchar
    have hfr_ne : Module.finrank ℂ (Representation.IntertwiningMap σ (ρ.comp H.subtype)) ≠ 0 :=
      fun h0 => hψ (by rw [hfr, h0, Nat.cast_zero])
    haveI : Nontrivial (Representation.IntertwiningMap σ (ρ.comp H.subtype)) :=
      Module.nontrivial_of_finrank_pos (Nat.pos_of_ne_zero hfr_ne)
    obtain ⟨f, hf⟩ := exists_ne (0 : Representation.IntertwiningMap σ (ρ.comp H.subtype))
    obtain ⟨N, hNsimple, hNchar⟩ :=
      exists_simpleSubmodule_character_eq_of_ne_zero_intertwiner ρ σ hf
    exact ⟨N, hNsimple, hNchar.trans hσchar.symm⟩
  intro θ η hθ hη
  obtain ⟨Nθ, hNθsimple, hNθchar⟩ := wrapper θ hθ
  obtain ⟨Nη, hNηsimple, hNηchar⟩ := wrapper η hη
  haveI := hNθsimple
  haveI := hNηsimple
  have hNη_ne : Nη ≠ ⊥ := Nη.nontrivial_iff_ne_bot.mp (IsSimpleModule.nontrivial ℂ[↥H] ↥Nη)
  obtain ⟨g, hg⟩ := character_conj_of_simpleSubmodule ρ Nη Nθ hNη_ne
  -- `hg : χ_{N_θ} = fun h => χ_{N_η} (g⁻¹ h g)`; substitute the constituent characters.
  rw [hNθchar, hNηchar] at hg
  refine ⟨g, ?_⟩
  apply IrreducibleCharacter.ext
  ext h
  rw [IrreducibleCharacter.coe_conjBy, ClassFunction.conjBy_apply]
  -- `θ(g h g⁻¹) = η(h)`: rewrite `θ` via `hg`, then `g⁻¹ (g h g⁻¹) g = h`.
  rw [hg]
  refine congrArg _ (Subtype.ext ?_)
  simp only [conjNormalMulAut_apply_coe]
  group

set_option backward.isDefEq.respectTransparency false in
/-- **Clifford's theorem, degree formula** ([Isaacs] Thm 6.5).  For a `G`-irreducible character `χ`,
a normal subgroup `H ⊴ G`, and a constituent `θ₀` of `Res^G_H χ`, the degree factors as
`χ(1) = ⟨Res χ, θ₀⟩ · [G : I_G(θ₀)] · θ₀(1)`.  Assembles the degree expansion
(`apply_one_eq_sum_restrictionMultiplicity_mul`), single-orbit
(`restrictionConstituentsSingleOrbit_of_isIrreducible`), common multiplicity
(`hasCommonRestrictionMultiplicity_of_singleOrbit`), and orbit size
(`card_conjByOrbit_eq_index_inertia`): in `∑_θ ⟨Res χ,θ⟩·θ(1)` only the `[G:I]`-element orbit of `θ₀`
contributes, each term equal to `⟨Res χ,θ₀⟩·θ₀(1)` (common multiplicity, conjugation-invariant
degree). -/
theorem apply_one_eq_restrictionMultiplicity_mul_index_inertia
    [Fintype G] [Invertible (Nat.card G : ℂ)]
    {H : Subgroup G} [hH : H.Normal] [Fintype ↥H] [Invertible (Nat.card ↥H : ℂ)]
    [Fintype (IrreducibleCharacter ↥H)]
    (χ : IrreducibleCharacter G) (θ₀ : IrreducibleCharacter ↥H)
    (hθ₀ : IrreducibleCharacter.LiesOver (G := G) (H := H) χ θ₀) :
    (χ : ClassFunction G ℂ) (1 : G)
      = ClassFunction.restrictionMultiplicity H (χ : ClassFunction G ℂ) (θ₀ : ClassFunction ↥H ℂ)
          * ((IrreducibleCharacter.inertia (G := G) (H := H) θ₀).index : ℂ)
          * (θ₀ : ClassFunction ↥H ℂ) 1 := by
  classical
  have hsingle := restrictionConstituentsSingleOrbit_of_isIrreducible (G := G) (H := H) χ
  have hcommon :=
    IrreducibleCharacter.hasCommonRestrictionMultiplicity_of_singleOrbit (H := H) hsingle
  rw [apply_one_eq_sum_restrictionMultiplicity_mul (H := H) (χ : ClassFunction G ℂ)]
  have key : ∀ θ : IrreducibleCharacter ↥H,
      ClassFunction.restrictionMultiplicity H (χ : ClassFunction G ℂ) (θ : ClassFunction ↥H ℂ)
          * (θ : ClassFunction ↥H ℂ) 1
        = if θ ∈ IrreducibleCharacter.conjByOrbit (G := G) (H := H) θ₀ then
            ClassFunction.restrictionMultiplicity H (χ : ClassFunction G ℂ)
                (θ₀ : ClassFunction ↥H ℂ) * (θ₀ : ClassFunction ↥H ℂ) 1
          else 0 := by
    intro θ
    by_cases hmem : θ ∈ IrreducibleCharacter.conjByOrbit (G := G) (H := H) θ₀
    · rw [if_pos hmem]
      obtain ⟨g, rfl⟩ := IrreducibleCharacter.mem_conjByOrbit.mp hmem
      rw [IrreducibleCharacter.HasCommonRestrictionMultiplicity.eq_of_liesOver hcommon
        (IrreducibleCharacter.liesOver_conjBy hθ₀ g) hθ₀, conjBy_apply_one]
    · rw [if_neg hmem]
      have hm0 : ClassFunction.restrictionMultiplicity H (χ : ClassFunction G ℂ)
          (θ : ClassFunction ↥H ℂ) = 0 := by
        by_contra hm
        exact hmem (IrreducibleCharacter.mem_conjByOrbit.mpr (hsingle θ₀ θ hθ₀ hm))
      rw [hm0, zero_mul]
  rw [Finset.sum_congr rfl (fun θ _ => key θ), ← Finset.sum_filter, Finset.sum_const,
    nsmul_eq_mul]
  have hcard : (Finset.univ.filter
      (fun θ => θ ∈ IrreducibleCharacter.conjByOrbit (G := G) (H := H) θ₀)).card
      = (IrreducibleCharacter.inertia (G := G) (H := H) θ₀).index := by
    rw [← card_conjByOrbit_eq_index_inertia (G := G) (H := H) θ₀,
      Nat.card_eq_fintype_card, ← Set.toFinset_card]
    congr 1
    ext θ
    simp [Set.mem_toFinset]
  rw [hcard]
  ring

end OddOrder.RepresentationTheory
