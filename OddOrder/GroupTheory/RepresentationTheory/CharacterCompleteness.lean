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

open Module (finrank)

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

end OddOrder.RepresentationTheory
