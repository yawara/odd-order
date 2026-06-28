/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.CliffordConjugateChar

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

end OddOrder.RepresentationTheory
