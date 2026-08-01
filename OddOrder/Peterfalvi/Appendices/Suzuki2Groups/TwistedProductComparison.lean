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
* `BilinearTwistedProduct.exists_mulEquiv_of_diag` — the comparison, together with its
  effect on the two coordinates; `nonempty_mulEquiv_of_diag` is the bare form.
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
theorem exists_mulEquiv_of_diag [Finite V] {B : BilinMap (ZMod 2) V W}
    {B' : BilinMap (ZMod 2) V' W'} (f : V ≃+ V') (g : W ≃+ W')
    (hdiag : ∀ x : V, B' (f x) (f x) = g (B x x)) :
    ∃ Ξ : BilinearTwistedProduct B ≃* BilinearTwistedProduct B',
      (∀ p : BilinearTwistedProduct B, (Ξ p).quotient = f p.quotient) ∧
      ∀ w : W, Ξ ⟨0, w⟩ = ⟨0, g w⟩ := by
  classical
  have hdiag' : ∀ x : V, comap B' f g x x = B x x := by
    intro x
    rw [comap_apply, hdiag, g.symm_apply_apply]
  have hcompat : ∀ x y : V, B' (f x) (f y) = g (comap B' f g x y) := by
    intro x y
    rw [comap_apply, g.apply_symm_apply]
  have hsq : ∀ e : BilinearTwistedProduct (comap B' f g), e ^ 2 =
      (groupExtension (comap B' f g)).inl
        (Multiplicative.ofAdd ((fun v => B v v)
          ((groupExtension (comap B' f g)).rightHom e).toAdd)) := by
    intro e
    have h := sq_eq_inl_diag (comap B' f g) e
    rwa [hdiag'] at h
  set Θ := GroupExtension.equivOfCommonSquareMap (groupExtension B)
    (groupExtension (comap B' f g)) centralEmbedding_range_le_center
    centralEmbedding_range_le_center (fun v => B v v)
    (Module.finBasis (ZMod 2) V) (fun e => sq_eq_inl_diag B e) hsq with hΘ
  refine ⟨Θ.toMulEquiv.trans (congrEquiv f g hcompat), fun p => ?_, fun w => ?_⟩
  · have h := congrFun Θ.rightHom_comm p
    have hq : (Θ.toMulEquiv p).quotient = p.quotient :=
      congrArg Multiplicative.toAdd h
    simp only [MulEquiv.trans_apply, congrEquiv_quotient, hq]
  · have h := congrFun Θ.inl_comm (Multiplicative.ofAdd w)
    have hw : Θ.toMulEquiv (⟨0, w⟩ : BilinearTwistedProduct B)
        = (⟨0, w⟩ : BilinearTwistedProduct (comap B' f g)) := h
    simp only [MulEquiv.trans_apply, hw]
    exact BilinearTwistedProduct.ext (map_zero f) rfl

/-- **Two twisted products whose diagonals correspond are isomorphic** — the bare
existence, for consumers that do not need the coordinates. -/
theorem nonempty_mulEquiv_of_diag [Finite V] {B : BilinMap (ZMod 2) V W}
    {B' : BilinMap (ZMod 2) V' W'} (f : V ≃+ V') (g : W ≃+ W')
    (hdiag : ∀ x : V, B' (f x) (f x) = g (B x x)) :
    Nonempty (BilinearTwistedProduct B ≃* BilinearTwistedProduct B') :=
  let ⟨Ξ, _, _⟩ := exists_mulEquiv_of_diag f g hdiag
  ⟨Ξ⟩

end BilinearTwistedProduct

end

end OddOrder.Peterfalvi.Appendices.Suzuki2Groups
