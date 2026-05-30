/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.RepresentationTheory.Subrepresentation
import Mathlib.GroupTheory.QuotientGroup.Basic
import OddOrder.GroupTheory.RepresentationTheory.IrrIndexing
import OddOrder.Peterfalvi.S03_PreliminaryCharacter

/-!
# Inflation of irreducible characters

For a surjective group homomorphism `f : H →* G`, precomposition of class functions
(`ClassFunction.compHom f`) carries irreducible characters of `G` to irreducible characters
of `H`, and preserves degrees.  Specialized to the quotient map `f = QuotientGroup.mk' N`
for a normal subgroup `N ⊴ G`, this is the classical **inflation** correspondence
([Isaacs] (2.22)): an irreducible character `χbar` of `G ⧸ N` inflates to the irreducible
character `χbar ∘ (mk' N)` of `G`, whose kernel contains `N`.

The representation-theoretic core is that for a surjective `f`, the lattice of
subrepresentations of `σ.comp f` coincides (identically on the underlying submodule) with that
of `σ`: a submodule invariant under all `σ (f h)` is invariant under all `σ g` because `f` is
onto.  Transporting `IsSimpleOrder` along the resulting order isomorphism gives irreducibility
preservation.  Trace (hence degree) is preserved because `σ.comp f` and `σ` act by the *same*
linear maps on the same space (`(σ.comp f) h = σ (f h)`).

This is the first brick of the Inflation infrastructure gating Peterfalvi (6.6) G2.5
(the degree-sum identity over the characters with `Z ⊆ ker`): the inflation map embeds
`Irr(G ⧸ N)` into `{χ ∈ Irr G | N ⊆ ker χ}` degree-preservingly, which feeds the
`Σ χ(1)²` bookkeeping via the Burnside identity `sumIrreducibleDegreeSq`.

## Main definitions / results

* `OddOrder.RepresentationTheory.Subrepresentation.compHomEquiv` — for surjective `f : H →* G`,
  the order isomorphism `Subrepresentation (σ.comp f) ≃o Subrepresentation σ`.
* `OddOrder.RepresentationTheory.Representation.isIrreducible_comp_of_surjective` — irreducibility
  of `σ` transfers to `σ.comp f` for surjective `f`.
* `OddOrder.RepresentationTheory.IsIrreducibleCharacter.compHom_of_surjective` — for surjective
  `f`, `ClassFunction.compHom f χ` is an irreducible character of `H` whenever `χ` is one of `G`.
* `OddOrder.RepresentationTheory.inflate` — the inflation map
  `IrreducibleCharacter (G ⧸ N) → IrreducibleCharacter G`, `χbar ↦ χbar ∘ (mk' N)`.
* `OddOrder.RepresentationTheory.inflate_apply_one` — degree preservation.
* `OddOrder.RepresentationTheory.subset_characterKernel_inflate` — `N ⊆ ker (inflate N χbar)`.

## References

* [Isaacs], *Character Theory of Finite Groups*, (2.22) (inflation / characters of `G ⧸ N`).
* Peterfalvi §6 (6.6) (degree-sum over `Z ⊆ ker`).
-/

namespace OddOrder.RepresentationTheory

namespace Subrepresentation

variable {G H V : Type*} [Group G] [Group H] [AddCommGroup V] [Module ℂ V]
  {f : H →* G}

/-- Push a subrepresentation of `σ.comp f` forward to a subrepresentation of `σ`, when `f` is
surjective.  The underlying submodule is unchanged; invariance under every `σ g` follows from
invariance under every `σ (f h)` because `f` is onto. -/
def ofCompSurjective (σ : Representation ℂ G V) (hf : Function.Surjective f)
    (R : Subrepresentation (σ.comp f)) : Subrepresentation σ where
  toSubmodule := R.toSubmodule
  apply_mem_toSubmodule g v hv := by
    obtain ⟨h, rfl⟩ := hf g
    exact R.apply_mem_toSubmodule h hv

/-- Pull a subrepresentation of `σ` back to a subrepresentation of `σ.comp f`.  The underlying
submodule is unchanged; invariance under `σ (f h)` is a special case of invariance under all
`σ g`. -/
def comapComp (σ : Representation ℂ G V) (R : Subrepresentation σ) :
    Subrepresentation (σ.comp f) where
  toSubmodule := R.toSubmodule
  apply_mem_toSubmodule h _v hv := R.apply_mem_toSubmodule (f h) hv

/-- For a surjective `f : H →* G`, the lattice of subrepresentations of `σ.comp f` is order
isomorphic to that of `σ`, identically on the underlying submodule. -/
def compHomEquiv (σ : Representation ℂ G V) (hf : Function.Surjective f) :
    Subrepresentation (σ.comp f) ≃o Subrepresentation σ where
  toFun := ofCompSurjective σ hf
  invFun := comapComp σ
  left_inv R := by cases R; rfl
  right_inv R := by cases R; rfl
  map_rel_iff' := Iff.rfl

end Subrepresentation

namespace Representation

variable {G H V : Type*} [Group G] [Group H] [AddCommGroup V] [Module ℂ V]
  {f : H →* G}

/-- **Irreducibility is preserved under surjective precomposition.** If `f : H →* G` is
surjective and `σ` is an irreducible representation of `G`, then `σ.comp f` is an irreducible
representation of `H`.

The proof transports `IsSimpleOrder (Subrepresentation σ)` (the definition of irreducibility)
along the order isomorphism `Subrepresentation.compHomEquiv`. -/
theorem isIrreducible_comp_of_surjective (σ : Representation ℂ G V)
    (hf : Function.Surjective f) (hσ : Representation.IsIrreducible σ) :
    Representation.IsIrreducible (σ.comp f) := by
  have : IsSimpleOrder (Subrepresentation σ) := hσ
  exact (Subrepresentation.compHomEquiv σ hf).isSimpleOrder

end Representation

variable {G H : Type*} [Group G] [Group H]

/-- **Inflation along a surjective homomorphism preserves irreducible characters.**
If `f : H →* G` is surjective and `φ` is an irreducible character of `G`, then its pullback
`ClassFunction.compHom f φ` is an irreducible character of `H`.

This is the homomorphism-general form of [Isaacs] (2.22): the witnessing irreducible
representation `σ` of `G` (with `φ = χ_σ`) precomposes to `σ.comp f`, which is irreducible by
`Representation.isIrreducible_comp_of_surjective` and whose character is `χ_σ ∘ f`, i.e. exactly
`compHom f φ`. -/
theorem IsIrreducibleCharacter.compHom_of_surjective {f : H →* G}
    (hf : Function.Surjective f) {φ : ClassFunction G ℂ}
    (hφ : IsIrreducibleCharacter φ) :
    IsIrreducibleCharacter (ClassFunction.compHom f φ) := by
  obtain ⟨V, _, _, _, σ, hσ, hχ⟩ := hφ
  refine ⟨V, inferInstance, inferInstance, inferInstance, σ.comp f,
    Representation.isIrreducible_comp_of_surjective σ hf hσ, ?_⟩
  funext h
  change φ (f h) = Representation.character (σ.comp f) h
  rw [show Representation.character (σ.comp f) h = σ.character (f h) from rfl,
    show (φ : G → ℂ) (f h) = σ.character (f h) from congrFun hχ (f h)]

section Inflation

variable (N : Subgroup G) [N.Normal]

/-- **Inflation map** ([Isaacs] (2.22)).  An irreducible character of `G ⧸ N` inflates to the
irreducible character of `G` obtained by precomposing with the quotient map `QuotientGroup.mk' N`.

`QuotientGroup.mk' N` is surjective, so `IsIrreducibleCharacter.compHom_of_surjective` provides
the irreducibility of the inflated character. -/
def inflate (χbar : IrreducibleCharacter (G ⧸ N)) : IrreducibleCharacter G :=
  ⟨ClassFunction.compHom (QuotientGroup.mk' N) (χbar : ClassFunction (G ⧸ N) ℂ),
    IsIrreducibleCharacter.compHom_of_surjective (QuotientGroup.mk'_surjective N)
      χbar.isIrreducible⟩

@[simp] theorem inflate_coe (χbar : IrreducibleCharacter (G ⧸ N)) :
    ((inflate N χbar : IrreducibleCharacter G) : ClassFunction G ℂ) =
      ClassFunction.compHom (QuotientGroup.mk' N) (χbar : ClassFunction (G ⧸ N) ℂ) :=
  rfl

@[simp] theorem inflate_apply (χbar : IrreducibleCharacter (G ⧸ N)) (g : G) :
    ((inflate N χbar : IrreducibleCharacter G) : ClassFunction G ℂ) g =
      (χbar : ClassFunction (G ⧸ N) ℂ) (QuotientGroup.mk' N g) :=
  rfl

/-- **Inflation preserves degree.** The inflated character evaluated at `1` equals the original
character of `G ⧸ N` evaluated at `1`: the quotient map sends `1` to `1`. -/
@[simp] theorem inflate_apply_one (χbar : IrreducibleCharacter (G ⧸ N)) :
    ((inflate N χbar : IrreducibleCharacter G) : ClassFunction G ℂ) 1 =
      (χbar : ClassFunction (G ⧸ N) ℂ) 1 := by
  rw [inflate_apply, map_one]

/-- **The kernel of an inflated character contains `N`** ([Isaacs] (2.22)).  Every `n ∈ N` maps
to `1` in `G ⧸ N`, so `(inflate N χbar) n = χbar 1 = (inflate N χbar) 1`, i.e. `n` lies in the
character kernel of `inflate N χbar`.

This places the image of the inflation map inside `{χ ∈ Irr G | N ⊆ ker χ}`, the set that the
Peterfalvi (6.6) degree-sum bookkeeping ranges over. -/
theorem subset_characterKernel_inflate (χbar : IrreducibleCharacter (G ⧸ N)) :
    (N : Set G) ⊆ OddOrder.Peterfalvi.S03.characterKernel
      ((inflate N χbar : IrreducibleCharacter G) : ClassFunction G ℂ) := by
  intro n hn
  rw [OddOrder.Peterfalvi.S03.mem_characterKernel,
    OddOrder.Peterfalvi.S03.characterDegree_def, inflate_apply, inflate_apply_one,
    (QuotientGroup.mk'_apply N n).trans ((QuotientGroup.eq_one_iff n).mpr hn)]

end Inflation

end OddOrder.RepresentationTheory
