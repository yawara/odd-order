/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.CenterClassSumBasis
import OddOrder.GroupTheory.RepresentationTheory.PermutationInvariants

/-!
# Orbit count for the σ-action on `Z(k[G])` via the class-sum basis

For Peterfalvi (9.1)'s kernel-FPF count (†), one of the two computations of
`dim Z(𝔽̄_p[U])^{⟨e⟩}` is via the **class-sum basis**: the automorphism `σ_e` permutes the
conjugacy classes, so by the cornerstone `finrank_invariants_eq_card_orbits` the invariant
dimension equals the number of `⟨e⟩`-orbits on classes.

This file builds the ingredients:
* functoriality of `ConjClasses.map` (`map_id`, `map_comp`);
* the action of `MulAut G` on `ConjClasses G` by `α • C = ConjClasses.map α C`;
* (to follow) the induced representation on `Z(k[G])` and the cornerstone application.
-/

open scoped MonoidAlgebra
open Module

namespace ConjClasses

/-- `ConjClasses.map` of the identity is the identity. -/
@[simp] theorem map_id {M : Type*} [Monoid M] (C : ConjClasses M) :
    ConjClasses.map (MonoidHom.id M) C = C := by
  obtain ⟨a, rfl⟩ := ConjClasses.mk_surjective C; rfl

/-- `ConjClasses.map` is functorial: `map f ∘ map g = map (f ∘ g)`. -/
theorem map_comp {M N P : Type*} [Monoid M] [Monoid N] [Monoid P]
    (f : N →* P) (g : M →* N) (C : ConjClasses M) :
    ConjClasses.map f (ConjClasses.map g C) = ConjClasses.map (f.comp g) C := by
  obtain ⟨a, rfl⟩ := ConjClasses.mk_surjective C; rfl

end ConjClasses

namespace OddOrder.GroupTheory.CenterClassSum

variable {G : Type*} [Group G]

/-- A group automorphism `α` acts on conjugacy classes by `α • C = ConjClasses.map α C`. -/
instance : MulAction (MulAut G) (ConjClasses G) where
  smul α C := ConjClasses.map (α : G →* G) C
  one_smul C := by obtain ⟨a, rfl⟩ := ConjClasses.mk_surjective C; rfl
  mul_smul α β C := by obtain ⟨a, rfl⟩ := ConjClasses.mk_surjective C; rfl

@[simp] theorem mulAut_smul_mk (α : MulAut G) (a : G) :
    α • (ConjClasses.mk a) = ConjClasses.mk (α a) := rfl

/-! ### The induced representation of `MulAut G` on `Z(k[G])` -/

/-- An algebra automorphism preserves the centre (`e z` commutes with everything, by transporting
the commutation of `z` with `e.symm w` through `e`). -/
theorem _root_.AlgEquiv.map_mem_center {k A : Type*} [CommSemiring k] [Semiring A] [Algebra k A]
    (e : A ≃ₐ[k] A) {z : A} (hz : z ∈ Subalgebra.center k A) :
    e z ∈ Subalgebra.center k A := by
  rw [Subalgebra.mem_center_iff] at hz ⊢
  intro w
  calc w * e z = e (e.symm w) * e z := by rw [e.apply_symm_apply]
    _ = e (e.symm w * z) := (map_mul e _ _).symm
    _ = e (z * e.symm w) := by rw [hz]
    _ = e z * e (e.symm w) := map_mul e _ _
    _ = e z * w := by rw [e.apply_symm_apply]

variable {k : Type*} [Field k]

/-- The endomorphism of `Z(k[G])` induced by `α : MulAut G` via `domCongr α`. -/
noncomputable def centerEnd (α : MulAut G) :
    Module.End k ↥(Subalgebra.center k (MonoidAlgebra k G)) where
  toFun z := ⟨MonoidAlgebra.domCongrAut (R := k) (A := k) α (z : MonoidAlgebra k G),
    (MonoidAlgebra.domCongrAut (R := k) (A := k) α).map_mem_center z.2⟩
  map_add' x y := by
    apply Subtype.ext
    show MonoidAlgebra.domCongrAut (R := k) (A := k) α
          ((x : MonoidAlgebra k G) + (y : MonoidAlgebra k G))
        = MonoidAlgebra.domCongrAut (R := k) (A := k) α (x : MonoidAlgebra k G)
          + MonoidAlgebra.domCongrAut (R := k) (A := k) α (y : MonoidAlgebra k G)
    rw [map_add]
  map_smul' c x := by
    apply Subtype.ext
    show MonoidAlgebra.domCongrAut (R := k) (A := k) α (c • (x : MonoidAlgebra k G))
        = c • MonoidAlgebra.domCongrAut (R := k) (A := k) α (x : MonoidAlgebra k G)
    rw [map_smul]

/-- The representation of `MulAut G` on the centre `Z(k[G])`: `α` acts by the algebra automorphism
`domCongr α` restricted to the centre. -/
noncomputable def centerRep :
    Representation k (MulAut G) ↥(Subalgebra.center k (MonoidAlgebra k G)) where
  toFun := centerEnd
  map_one' := by
    apply LinearMap.ext; intro z; apply Subtype.ext
    show MonoidAlgebra.domCongrAut (R := k) (A := k) (1 : MulAut G) (z : MonoidAlgebra k G)
        = (z : MonoidAlgebra k G)
    rw [map_one, AlgEquiv.one_apply]
  map_mul' α β := by
    apply LinearMap.ext; intro z; apply Subtype.ext
    show MonoidAlgebra.domCongrAut (R := k) (A := k) (α * β) (z : MonoidAlgebra k G)
        = MonoidAlgebra.domCongrAut (R := k) (A := k) α
            (MonoidAlgebra.domCongrAut (R := k) (A := k) β (z : MonoidAlgebra k G))
    rw [map_mul, AlgEquiv.mul_apply]

/-! ### The cornerstone applied to the class-sum basis -/

variable [Fintype G] [DecidableEq G] [Fintype (ConjClasses G)] [DecidableEq (ConjClasses G)]

/-- `centerRep` permutes the class-sum basis according to the `MulAut G`-action on classes:
`centerRep α (centerBasis C) = centerBasis (α • C)`.  This is `domCongr_classSum` transported to the
centre subalgebra. -/
theorem centerRep_apply_centerBasis (α : MulAut G) (C : ConjClasses G) :
    centerRep (k := k) α (centerBasis (k := k) C) = centerBasis (k := k) (α • C) := by
  rw [centerBasis_apply, centerBasis_apply]
  apply Subtype.ext
  show MonoidAlgebra.domCongrAut (R := k) (A := k) α (classSum (k := k) C)
      = classSum (k := k) (ConjClasses.map (α : G →* G) C)
  exact domCongr_classSum α C

/-
**TODO (next): the cornerstone application.**  The orbit count
`finrank k ↥(Representation.invariants centerRep) = Nat.card (orbitRel.Quotient (MulAut G) (ConjClasses G))`
is exactly `PermutationInvariants.finrank_invariants_eq_card_orbits centerBasis centerRep
centerRep_apply_centerBasis`.  The mathematics is complete — `centerRep_apply_centerBasis` is the
compatibility hypothesis the cornerstone requires.  What blocks it is a Lean elaboration blowup: even
*stating* `↥(Representation.invariants centerRep)` over the heavy coercion tower
`↥(Subalgebra.center k (MonoidAlgebra k G))` loops at `isDefEq`/`whnf` past 1M heartbeats (marking
`centerEnd`/`centerRep` `irreducible` does not help — the cost is in the subalgebra/coe instances, not
in unfolding the defs).  Likely resolution: introduce a type synonym (or `Module`-level wrapper) for
the centre so the coercion tower is opaque, then apply the cornerstone through it.
-/

end OddOrder.GroupTheory.CenterClassSum
