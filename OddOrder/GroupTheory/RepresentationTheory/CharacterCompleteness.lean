/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import OddOrder.GroupTheory.RepresentationTheory.CharacterCount

/-!
# Completeness of irreducible characters (work in progress)

Toward `|Irr G| = |ConjClasses G|`: the irreducible characters span the space of class
functions. The strategy (analytic / regular-representation route) attaches to a class
function `f` and a representation `ρ` the operator `T_ρ f = ∑_g f(g) • ρ(g) : End V`.

* `classFunctionOperator` — the operator `∑_g f(g) • ρ(g)`.
* `classFunctionOperator_comm` — because `f` is a class function, `T_ρ f` commutes with
  every `ρ(h)`, i.e. it is a `G`-intertwiner of `ρ`.

By Schur's lemma, on an irreducible `ρ` the intertwiner `T_ρ f` is a scalar, computable from
the inner product `(f, χ_ρ)`; if `f ⊥ Irr G` then this scalar is `0`, so `T_ρ f = 0` on every
irreducible and (by Maschke) on the regular representation, forcing `f = 0`. Hence the
irreducible characters span, giving `|Irr G| ≥ |ConjClasses G|` and (with the reverse
inequality already proved) equality. The downstream steps are not yet formalized here.
-/

namespace OddOrder.RepresentationTheory

open Module (finrank)

section CFOp

variable {G V : Type*} [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V]

/-- The operator `∑_{g ∈ G} f(g) • ρ(g)` attached to a class function `f` and a
representation `ρ`, as an endomorphism of `V`. -/
noncomputable def classFunctionOperator (f : ClassFunction G ℂ) (ρ : Representation ℂ G V) :
    Module.End ℂ V :=
  ∑ g : G, f g • ρ g

/-- The class-function operator commutes with the representation: `ρ(h) ∘ T = T ∘ ρ(h)`.
This is the `G`-intertwiner property, and it holds precisely because `f` is constant on
conjugacy classes. -/
theorem classFunctionOperator_comm (f : ClassFunction G ℂ) (ρ : Representation ℂ G V) (h : G) :
    ρ h * classFunctionOperator f ρ = classFunctionOperator f ρ * ρ h := by
  unfold classFunctionOperator
  rw [Finset.mul_sum, Finset.sum_mul]
  -- LHS term: ρ h * (f g • ρ g) = f g • ρ (h * g); RHS term: (f g • ρ g) * ρ h = f g • ρ (g * h)
  have hL : ∀ g : G, ρ h * (f g • ρ g) = f g • ρ (h * g) := by
    intro g; rw [mul_smul_comm, ← map_mul]
  have hR : ∀ g : G, (f g • ρ g) * ρ h = f g • ρ (g * h) := by
    intro g; rw [smul_mul_assoc, ← map_mul]
  rw [Finset.sum_congr rfl (fun g _ => hL g), Finset.sum_congr rfl (fun g _ => hR g)]
  -- Goal: ∑ g, f g • ρ (h * g) = ∑ g, f g • ρ (g * h).
  -- Reindex the RHS by conjugation `g ↦ h * g * h⁻¹`, which sends `g * h ↦ h * g` and fixes `f`.
  rw [← Equiv.sum_comp (MulAut.conj h).toEquiv (fun g => f g • ρ (g * h))]
  refine Finset.sum_congr rfl (fun g _ => ?_)
  have hconj : (MulAut.conj h).toEquiv g = h * g * h⁻¹ := by simp [MulAut.conj_apply]
  rw [hconj, f.conj_eq g h, show h * g * h⁻¹ * h = h * g from by group]

/-- The class-function operator `T_ρ f`, packaged as an `IntertwiningMap ρ ρ`
(`classFunctionOperator_comm` is exactly the intertwining condition). -/
noncomputable def classFunctionIntertwiner (f : ClassFunction G ℂ) (ρ : Representation ℂ G V) :
    Representation.IntertwiningMap ρ ρ :=
  (classFunctionOperator f ρ).intertwiningMap_of_isIntertwiningMap ρ ρ (by
    intro g v
    have h := classFunctionOperator_comm f ρ g
    have h2 := (LinearMap.congr_fun h v).symm
    simpa only [Module.End.mul_apply] using h2)

@[simp] theorem classFunctionIntertwiner_toLinearMap (f : ClassFunction G ℂ)
    (ρ : Representation ℂ G V) :
    (classFunctionIntertwiner f ρ).toLinearMap = classFunctionOperator f ρ := rfl

/-- **Schur's lemma (scalar form).** On a finite-dimensional irreducible complex
representation, the class-function operator `T_ρ f` is a scalar multiple of the identity. -/
theorem classFunctionOperator_eq_smul_id [FiniteDimensional ℂ V] (f : ClassFunction G ℂ)
    (ρ : Representation ℂ G V) [Representation.IsIrreducible ρ] :
    ∃ c : ℂ, classFunctionOperator f ρ = c • LinearMap.id := by
  obtain ⟨c, hc⟩ :=
    (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
      (ρ := ρ)).surjective (classFunctionIntertwiner f ρ)
  refine ⟨c, ?_⟩
  have hL : classFunctionOperator f ρ
      = (algebraMap ℂ (Representation.IntertwiningMap ρ ρ) c).toLinearMap := by
    rw [hc]; rfl
  rw [hL, Representation.IntertwiningMap.algebraMap_apply,
    Representation.IntertwiningMap.toLinearMap_smul]
  congr 1

/-- The trace of `T_ρ f = ∑_g f(g) • ρ(g)` is `∑_g f(g) · χ_ρ(g)`. -/
theorem trace_classFunctionOperator [FiniteDimensional ℂ V] (f : ClassFunction G ℂ)
    (ρ : Representation ℂ G V) :
    LinearMap.trace ℂ V (classFunctionOperator f ρ) = ∑ g : G, f g * ρ.character g := by
  unfold classFunctionOperator
  rw [map_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [map_smul, smul_eq_mul]
  rfl

/-- If `∑_g f(g) · χ_ρ(g) = 0` for a finite-dimensional irreducible representation `ρ`, then the
class-function operator `T_ρ f` vanishes: by Schur it is `c • id`, and the trace forces `c = 0`. -/
theorem classFunctionOperator_eq_zero_of_sum_eq_zero [FiniteDimensional ℂ V] [Nontrivial V]
    (f : ClassFunction G ℂ) (ρ : Representation ℂ G V) [Representation.IsIrreducible ρ]
    (h : ∑ g : G, f g * ρ.character g = 0) :
    classFunctionOperator f ρ = 0 := by
  obtain ⟨c, hc⟩ := classFunctionOperator_eq_smul_id f ρ
  have hfr : 0 < finrank ℂ V := Module.finrank_pos
  have htr : c * (finrank ℂ V : ℂ) = 0 := by
    have e1 : LinearMap.trace ℂ V (classFunctionOperator f ρ) = c * (finrank ℂ V : ℂ) := by
      rw [hc, map_smul, LinearMap.trace_id, smul_eq_mul]
    rw [trace_classFunctionOperator] at e1
    rw [← e1, h]
  have hc0 : c = 0 := by
    rcases mul_eq_zero.mp htr with hc0 | hfr0
    · exact hc0
    · exact absurd (Nat.cast_eq_zero.mp hfr0) hfr.ne'
  rw [hc, hc0, zero_smul]

end CFOp

section Transfer

variable {G : Type*} [Group G]

/-- Transport a representation `σ` on `W` along a linear equivalence `e : W ≃ₗ[ℂ] X`, giving a
representation on `X` (conjugation by `e`). Used to move a finite-dimensional representation to a
representative on `Fin n → ℂ`, a `Type 0` space. -/
noncomputable def transportRep {W X : Type*} [AddCommGroup W] [Module ℂ W]
    [AddCommGroup X] [Module ℂ X] (σ : Representation ℂ G W) (e : W ≃ₗ[ℂ] X) :
    Representation ℂ G X :=
  ((e.conjRingEquiv : Module.End ℂ W ≃+* Module.End ℂ X).toRingHom.toMonoidHom).comp σ

@[simp] theorem transportRep_apply {W X : Type*} [AddCommGroup W] [Module ℂ W]
    [AddCommGroup X] [Module ℂ X] (σ : Representation ℂ G W) (e : W ≃ₗ[ℂ] X) (g : G) :
    transportRep σ e g = e.conj (σ g) := rfl

/-- Transporting a representation preserves its character. -/
theorem transportRep_character {W X : Type*} [AddCommGroup W] [Module ℂ W]
    [AddCommGroup X] [Module ℂ X] [FiniteDimensional ℂ W]
    (σ : Representation ℂ G W) (e : W ≃ₗ[ℂ] X) :
    (transportRep σ e).character = σ.character := by
  funext g
  show LinearMap.trace ℂ X (e.conj (σ g)) = LinearMap.trace ℂ W (σ g)
  exact LinearMap.trace_conj' (σ g) e

set_option backward.isDefEq.respectTransparency false in
/-- Transporting an irreducible representation along a linear equivalence keeps it irreducible. -/
theorem transportRep_isIrreducible {W X : Type*} [AddCommGroup W] [Module ℂ W]
    [AddCommGroup X] [Module ℂ X] (σ : Representation ℂ G W) (e : W ≃ₗ[ℂ] X)
    [Representation.IsIrreducible σ] : Representation.IsIrreducible (transportRep σ e) := by
  -- rep equivalence `σ ≃ transportRep σ e` via `e`
  have he : ∀ g : G, (e : W →ₗ[ℂ] X) ∘ₗ σ g = (transportRep σ e) g ∘ₗ (e : W →ₗ[ℂ] X) := by
    intro g; ext w
    simp only [LinearMap.comp_apply, transportRep_apply, LinearEquiv.conj_apply_apply,
      LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  let φ : σ.Equiv (transportRep σ e) := Representation.Equiv.mk e he
  -- transport to `asModule` linear equivalence over `ℂ[G]`
  have hbij : Function.Bijective
      (Representation.IntertwiningMap.equivLinearMapAsModule σ (transportRep σ e)
        φ.toIntertwiningMap) :=
    e.bijective
  -- No type annotation on `L`: the `asModule` `MonoidAlgebra`-module instance is baked into the
  -- result of `equivLinearMapAsModule`, whereas re-stating the type would re-trigger (and fail)
  -- instance search on the `asModule` type synonym.
  let L := LinearEquiv.ofBijective
      (Representation.IntertwiningMap.equivLinearMapAsModule σ (transportRep σ e)
        φ.toIntertwiningMap) hbij
  haveI hσs := (Representation.irreducible_iff_isSimpleModule_asModule σ).mp
    ‹Representation.IsIrreducible σ›
  rw [Representation.irreducible_iff_isSimpleModule_asModule]
  exact IsSimpleModule.congr L.symm

/-- **Every finite-dimensional irreducible complex representation has its character among the
`IsIrreducibleCharacter`s.** (`IsIrreducibleCharacter` only quantifies over `Type 0` carriers;
this discharges the universe restriction by transporting to `Fin n → ℂ`.) -/
theorem exists_isIrreducibleCharacter_eq {W : Type*} [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] (σ : Representation ℂ G W) [Representation.IsIrreducible σ] :
    ∃ φ : ClassFunction G ℂ, IsIrreducibleCharacter φ ∧ (φ : G → ℂ) = σ.character := by
  let e : W ≃ₗ[ℂ] (Fin (finrank ℂ W) → ℂ) := (Module.finBasis ℂ W).equivFun
  haveI : Representation.IsIrreducible (transportRep σ e) := transportRep_isIrreducible σ e
  refine ⟨repCharacterClassFunction (transportRep σ e),
    ⟨Fin (finrank ℂ W) → ℂ, inferInstance, inferInstance, inferInstance, transportRep σ e,
      inferInstance, rfl⟩, ?_⟩
  funext g
  exact congrFun (transportRep_character σ e) g

end Transfer

end OddOrder.RepresentationTheory
