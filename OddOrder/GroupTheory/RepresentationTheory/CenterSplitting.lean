/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.CenterOrbitCount

/-!
# Transporting the centre along an algebra isomorphism

For Peterfalvi (9.1)'s orbit-count Brauer lemma, the splitting `Z(𝔽̄_p[U]) ≅ (Fin N → k)` is built
by transporting the centre through the Wedderburn decomposition `k[U] ≅ ∏ᵢ Matᵢ(k)`.  The first
link is the basis-free fact that an algebra isomorphism `e : A ≃ₐ[R] B` restricts to an isomorphism
of centres, `Z(A) ≃ₐ[R] Z(B)`.

`AlgEquiv.map_mem_center` (in `CenterOrbitCount`) already gives that `e` carries the centre *into*
the centre; here we package the two-sided statement as an `AlgEquiv`.
-/

namespace OddOrder.GroupTheory.CenterSplitting

variable {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]

/-- An algebra isomorphism carries the centre *onto* the centre. -/
theorem center_map_eq (e : A ≃ₐ[R] B) :
    (Subalgebra.center R A).map (e : A →ₐ[R] B) = Subalgebra.center R B := by
  apply le_antisymm
  · rw [Subalgebra.map_le]
    intro x hx
    exact e.map_mem_center hx
  · intro y hy
    refine Subalgebra.mem_map.mpr ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    exact e.symm.map_mem_center hy

/-- **An algebra isomorphism restricts to an isomorphism of centres** `Z(A) ≃ₐ[R] Z(B)`. -/
def _root_.AlgEquiv.centerCongr (e : A ≃ₐ[R] B) :
    Subalgebra.center R A ≃ₐ[R] Subalgebra.center R B :=
  (e.subalgebraMap (Subalgebra.center R A)).trans
    (Subalgebra.equivOfEq _ _ (center_map_eq e))

@[simp] theorem centerCongr_apply (e : A ≃ₐ[R] B) (x : Subalgebra.center R A) :
    (e.centerCongr x : B) = e (x : A) := rfl

end OddOrder.GroupTheory.CenterSplitting
