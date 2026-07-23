/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.ExponentTwoGraphSubspaceGeometry
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaThirteen.ExponentTwoGraphSubspaceInvariant

/-!
# Higman's Lemma 13: a graph over a third coordinate axis

G. Higman, “Suzuki 2-groups,” *Illinois Journal of Mathematics* 7 (1963),
Lemma 13, p. 93.

Starting from a nontrivial graph across two disjoint factor axes, this file
adds an arbitrary multiple of a third axis.  The resulting three-term graph
remains injective and disjoint from the third axis.  Adjoining that axis
recovers exactly the sum of the original graph and the axis, so the latter
sum's properness is preserved.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

universe uV

/-- Let `gXZ(α) = iX(aα) + iZ(bα)` for a nonzero coefficient pair and let
`d(α) = gXZ(α) + iT(cα)`.  If the first two axes are disjoint and their sum
is disjoint from the target axis, then `d` is an injective graph over
`gXZ`, remains disjoint from the target axis, and generates the same
subspace after that axis is adjoined. -/
theorem threeTermGraphOverTargetAxis_geometry
    {n : ℕ}
    {V : Type uV} [AddCommGroup V] [Module (ZMod 2) V]
    (iX iZ iT : GaloisField 2 n →ₗ[ZMod 2] V)
    (hiX : Function.Injective iX)
    (hiZ : Function.Injective iZ)
    (hiT : Function.Injective iT)
    (hXZ :
      LinearMap.range iX ⊓ LinearMap.range iZ = ⊥)
    (hXZ_T :
      (LinearMap.range iX ⊔ LinearMap.range iZ) ⊓
        LinearMap.range iT = ⊥)
    (a b c : GaloisField 2 n)
    (hab : a ≠ 0 ∨ b ≠ 0) :
    let gXZ := commonEigenvalueGraphMap iX iZ a b
    let d := commonEigenvalueGraphMap gXZ iT 1 c
    Function.Injective gXZ ∧
      LinearMap.range gXZ ≠ ⊥ ∧
      LinearMap.range gXZ ⊓ LinearMap.range iT = ⊥ ∧
      Function.Injective d ∧
      LinearMap.range d ≠ ⊥ ∧
      LinearMap.range d <
        LinearMap.range gXZ ⊔ LinearMap.range iT ∧
      LinearMap.range d ⊓ LinearMap.range iT = ⊥ ∧
      LinearMap.range d ⊔ LinearMap.range iT =
        LinearMap.range gXZ ⊔ LinearMap.range iT ∧
      LinearMap.range d ⊔ LinearMap.range iT ≠ ⊤ := by
  let gXZ := commonEigenvalueGraphMap iX iZ a b
  let d := commonEigenvalueGraphMap gXZ iT 1 c
  change
    Function.Injective gXZ ∧
      LinearMap.range gXZ ≠ ⊥ ∧
      LinearMap.range gXZ ⊓ LinearMap.range iT = ⊥ ∧
      Function.Injective d ∧
      LinearMap.range d ≠ ⊥ ∧
      LinearMap.range d <
        LinearMap.range gXZ ⊔ LinearMap.range iT ∧
      LinearMap.range d ⊓ LinearMap.range iT = ⊥ ∧
      LinearMap.range d ⊔ LinearMap.range iT =
        LinearMap.range gXZ ⊔ LinearMap.range iT ∧
      LinearMap.range d ⊔ LinearMap.range iT ≠ ⊤
  obtain ⟨hgInj, hgNeBot, _, hgTbot, hgTtop⟩ :=
    graphSubspace_geometry iX iZ hiX hiZ hXZ a b hab
      gXZ (fun _ ↦ rfl) (LinearMap.range iT) hXZ_T
  obtain ⟨hdInj, hdNeBot, hdLt, _, _⟩ :=
    graphSubspace_geometry gXZ iT hgInj hiT hgTbot 1 c
      (Or.inl one_ne_zero) d (fun _ ↦ rfl) ⊥ (by simp)
  have hdTbot :
      LinearMap.range d ⊓ LinearMap.range iT =
        (⊥ : Submodule (ZMod 2) V) := by
    apply le_bot_iff.mp
    rintro _ ⟨⟨alpha, rfl⟩, hdAlphaT⟩
    have hiTc :
        iT (c * alpha) ∈ LinearMap.range iT :=
      ⟨c * alpha, rfl⟩
    have hgAlphaT : gXZ alpha ∈ LinearMap.range iT := by
      have hsub := sub_mem hdAlphaT hiTc
      simpa [d, commonEigenvalueGraphMap_apply] using hsub
    have hgAlphaBoth :
        gXZ alpha ∈
          LinearMap.range gXZ ⊓ LinearMap.range iT :=
      ⟨⟨alpha, rfl⟩, hgAlphaT⟩
    have hgAlphaZero : gXZ alpha = 0 := by
      rw [hgTbot] at hgAlphaBoth
      simpa only [Submodule.mem_bot] using hgAlphaBoth
    have hAlphaZero : alpha = 0 :=
      hgInj (by simpa only [map_zero] using hgAlphaZero)
    subst alpha
    simp [d]
  have hdLe :
      LinearMap.range d ≤
        LinearMap.range gXZ ⊔ LinearMap.range iT := by
    rintro _ ⟨alpha, rfl⟩
    simpa only [d, commonEigenvalueGraphMap_apply, one_mul] using
      add_mem
      ((show LinearMap.range gXZ ≤
          LinearMap.range gXZ ⊔ LinearMap.range iT from le_sup_left)
        (show gXZ alpha ∈ LinearMap.range gXZ from ⟨alpha, rfl⟩))
      ((show LinearMap.range iT ≤
          LinearMap.range gXZ ⊔ LinearMap.range iT from le_sup_right)
        (show iT (c * alpha) ∈ LinearMap.range iT from
          ⟨c * alpha, rfl⟩))
  have hgLe :
      LinearMap.range gXZ ≤
        LinearMap.range d ⊔ LinearMap.range iT := by
    rintro _ ⟨alpha, rfl⟩
    have hdAlpha :
        d alpha ∈
          LinearMap.range d ⊔ LinearMap.range iT :=
      (show LinearMap.range d ≤
          LinearMap.range d ⊔ LinearMap.range iT from le_sup_left)
        (show d alpha ∈ LinearMap.range d from ⟨alpha, rfl⟩)
    have hiTc :
        iT (c * alpha) ∈
          LinearMap.range d ⊔ LinearMap.range iT :=
      (show LinearMap.range iT ≤
          LinearMap.range d ⊔ LinearMap.range iT from le_sup_right)
        (show iT (c * alpha) ∈ LinearMap.range iT from
          ⟨c * alpha, rfl⟩)
    have hsub := sub_mem hdAlpha hiTc
    simpa [d, commonEigenvalueGraphMap_apply] using hsub
  have hsup :
      LinearMap.range d ⊔ LinearMap.range iT =
        LinearMap.range gXZ ⊔ LinearMap.range iT := by
    apply le_antisymm
    · exact sup_le hdLe le_sup_right
    · exact sup_le hgLe le_sup_right
  have hdTtop :
      LinearMap.range d ⊔ LinearMap.range iT ≠
        (⊤ : Submodule (ZMod 2) V) := by
    rw [hsup]
    exact hgTtop
  exact
    ⟨hgInj, hgNeBot, hgTbot, hdInj, hdNeBot, hdLt, hdTbot,
      hsup, hdTtop⟩

end OddOrder.Higman.Suzuki2Groups
