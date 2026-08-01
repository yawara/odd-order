/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.CentralElementaryExtension
import OddOrder.Peterfalvi.Appendices.Suzuki2Groups.QuadraticExtensions

/-!
# Twisted products with corresponding diagonals are isomorphic

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
Appendix III, Lemma 1(c), p. 140.

A twisted product `BilinearTwistedProduct B` over `𝐅₂` depends on the cocycle `B`
only through its **diagonal** `v ↦ B v v`, which is the squaring map of the group.
Two bilinear lifts of the same quadratic map therefore give isomorphic groups; this
file states that in the form needed to compare two *different* coordinate systems,
namely along a pair of additive equivalences `f : V ≃+ V'`, `g : W ≃+ W'` matching
the two diagonals.

Peterfalvi Part II, Ch. IV §3 (4) needs exactly this: Chapter III §3 presents `Q` as
the twisted product of an anisotropic cocycle `φ` on `E = 𝐅_{q²}`, while Chapter IV
works in the unitary coordinates of `PSU(3, q)`, whose cocycle is the Hermitian one;
the two diagonals are matched by
`OddOrder.FiniteField.exists_addEquiv_norm_of_anisotropic`.

## Main results

* `BilinearTwistedProduct.comap` — pull a cocycle back along a pair of coordinate
  equivalences.
* `BilinearTwistedProduct.nonempty_mulEquiv_of_diag` — the comparison.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki2Groups

noncomputable section

open LinearMap (BilinMap)

namespace BilinearTwistedProduct

variable {V W V' W' : Type*} [AddCommGroup V] [AddCommGroup W]
  [AddCommGroup V'] [AddCommGroup W']
  [Module (ZMod 2) V] [Module (ZMod 2) W] [Module (ZMod 2) V'] [Module (ZMod 2) W']

/-- **Pull a cocycle back along a pair of coordinate equivalences.**  Additive maps
between `𝐅₂`-modules are automatically linear, so no linearity hypothesis is needed
on `f` and `g`. -/
def comap (B' : BilinMap (ZMod 2) V' W') (f : V ≃+ V') (g : W ≃+ W') :
    BilinMap (ZMod 2) V W :=
  (B'.compl₁₂ (f.toAddMonoidHom.toZModLinearMap 2)
      (f.toAddMonoidHom.toZModLinearMap 2)).compr₂
    (g.symm.toAddMonoidHom.toZModLinearMap 2)

@[simp] theorem comap_apply (B' : BilinMap (ZMod 2) V' W') (f : V ≃+ V') (g : W ≃+ W')
    (x y : V) : comap B' f g x y = g.symm (B' (f x) (f y)) :=
  rfl

/-- **Two twisted products whose diagonals correspond are isomorphic.**

The isomorphism is not `(x, w) ↦ (f x, g w)` — that is one only when `f` and `g`
match the cocycles themselves, not just their diagonals (`congrEquiv`).  What is true
in general is that both groups are central extensions of `W` by `V` with the same
squaring map, and Appendix III, Lemma 1(c) (here
`GroupExtension.equivOfCommonSquareMap`) identifies those. -/
theorem nonempty_mulEquiv_of_diag [Finite V] {B : BilinMap (ZMod 2) V W}
    {B' : BilinMap (ZMod 2) V' W'} (f : V ≃+ V') (g : W ≃+ W')
    (hdiag : ∀ x : V, B' (f x) (f x) = g (B x x)) :
    Nonempty (BilinearTwistedProduct B ≃* BilinearTwistedProduct B') := by
  classical
  have hdiag' : ∀ x : V, comap B' f g x x = B x x := by
    intro x
    rw [comap_apply, hdiag, g.symm_apply_apply]
  have hcompat : ∀ x y : V, B' (f x) (f y) = g (comap B' f g x y) := by
    intro x y
    rw [comap_apply, g.apply_symm_apply]
  refine ⟨(GroupExtension.equivOfCommonSquareMap (groupExtension B)
    (groupExtension (comap B' f g)) centralEmbedding_range_le_center
    centralEmbedding_range_le_center (fun v => B v v)
    (Module.finBasis (ZMod 2) V) (fun e => sq_eq_inl_diag B e) ?_).toMulEquiv.trans
      (congrEquiv f g hcompat)⟩
  intro e
  have h := sq_eq_inl_diag (comap B' f g) e
  rwa [hdiag'] at h

end BilinearTwistedProduct

end

end OddOrder.Peterfalvi.Appendices.Suzuki2Groups
