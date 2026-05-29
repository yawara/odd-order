/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
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

end OddOrder.RepresentationTheory
