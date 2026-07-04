/-
Copyright (c) 2026 Yawara ISHIDA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddOrder.Peterfalvi.S09_CrossOrthogonality
import OddOrder.Peterfalvi.S09_FrobeniusHypothesis79

/-!
# `hzeta_cross` from conjugate images (Peterfalvi (7.9), coq `disjoint_coherent_ortho`)

The `Hypothesis79`-level bridge from the abstract cross-orthogonality primitive
`orthonormal_vchar_diff_ortho` (`S09_CrossOrthogonality`) to the `hzeta_cross` input
(`⟨ζ₁^{ν₁}, ζ₂^{ν₂}⟩ = 0`) of the (7.9) `conclusion` dichotomy.

The support route `zetaImage_cross_eq_zero_of_support_subset` is inapplicable because coherent
images are `±`-irreducibles with (essentially) full support.  Instead, feed the primitive with the
conjugate images `b = ζ̄₁^{ν₁}`, `d = ζ̄₂^{ν₂}`: the isometry of `ν` makes `{ζ₁^ν, ζ̄₁^ν}` and
`{ζ₂^ν, ζ̄₂^ν}` orthonormal, and the coherent extension agrees with the Dade isometry on the
equal-degree differences, so

* `ζ₁^ν − ζ̄₁^ν = τ₁(ζ₁ − ζ̄₁)` is supported in the Dade support `A₁^{τ₁}`, and likewise for `2`;
* those two Dade supports are **disjoint** (`Hypothesis79.dadeSupport_disjoint`), giving
  `⟨ζ₁^ν − ζ̄₁^ν, ζ₂^ν − ζ̄₂^ν⟩ = 0` (the same computation as `beta_inner_beta_eq_zero`);
* each difference vanishes at `1` since `1 ∉ A₁^{τ₁}` (`one_notMem_dadeSupport`) — equal degree.

This mirrors coq `disjoint_coherent_ortho` (`PFsection7.v`), which reduces to
`orthonormal_vchar_diff_ortho` (`PFsection4.v`) exactly as here.  The conjugate-image data
(`hbZ`, `hbn`, `hab`, `hab_supp`, …) is supplied at the Frobenius level from `F.coherence`
(isometry `nu_isometry`, agreement `coherence_extension_sub_eq_of_support`, conjugate-closure of the
Sibley induced family).
-/

namespace OddOrder.Peterfalvi.S09

open OddOrder.RepresentationTheory

namespace Hypothesis79

variable {G : Type*} [Group G] [Fintype G]
variable {A₁ : Set G} {L₁ : Subgroup G} [Fintype L₁] [Invertible (Nat.card L₁ : ℂ)]
variable {A₂ : Set G} {L₂ : Subgroup G} [Fintype L₂]
variable [Invertible (Nat.card L₂ : ℂ)] [Invertible (Nat.card G : ℂ)]

/-- **Cross-orthogonality of the two distinguished coherent images** (Peterfalvi (7.9);
coq `disjoint_coherent_ortho`).  Given the conjugate images `b = ζ̄₁^{ν₁}`, `d = ζ̄₂^{ν₂}` with

* `b, d ∈ ℤ[Irr G]`, both of norm `1`, orthogonal to `ζ₁^{ν₁}`, `ζ₂^{ν₂}` respectively
  (`{ζ_i^ν, ζ̄_i^ν}` orthonormal — the isometry of `ν`), and
* the differences `ζ_i^ν − ζ̄_i^ν` supported in the two **disjoint** Dade supports
  `A_i^{τ_i}` (`Hypothesis79.dadeSupport_disjoint`; the coherent extension agrees with `τ_i` on the
  equal-degree difference),

the two distinguished images are orthogonal: `⟨ζ₁^{ν₁}, ζ₂^{ν₂}⟩ = 0`.  The `hzeta_cross` input of
the (7.9) `conclusion` producers, discharged via `orthonormal_vchar_diff_ortho`. -/
theorem zetaImage_cross_eq_zero_of_conjugate_images (H79 : Hypothesis79 G A₁ L₁ A₂ L₂)
    {b d : ClassFunction G ℂ}
    (haZ : H79.firstZetaImage ∈ ZIrr G) (hbZ : b ∈ ZIrr G)
    (hcZ : H79.secondZetaImage ∈ ZIrr G) (hdZ : d ∈ ZIrr G)
    (han : ClassFunction.inner H79.firstZetaImage H79.firstZetaImage = 1)
    (hbn : ClassFunction.inner b b = 1)
    (hcn : ClassFunction.inner H79.secondZetaImage H79.secondZetaImage = 1)
    (hdn : ClassFunction.inner d d = 1)
    (hab : ClassFunction.inner H79.firstZetaImage b = 0)
    (hcd : ClassFunction.inner H79.secondZetaImage d = 0)
    (hab_supp :
      (H79.firstZetaImage - b).support ⊆ H79.first.hyp76.hyp71.hyp.dadeSupport)
    (hcd_supp :
      (H79.secondZetaImage - d).support ⊆ H79.second.hyp76.hyp71.hyp.dadeSupport) :
    ClassFunction.inner H79.firstZetaImage H79.secondZetaImage = 0 := by
  refine orthonormal_vchar_diff_ortho haZ hbZ hcZ hdZ han hbn hcn hdn hab hcd ?_ ?_ ?_
  · -- `⟨ζ₁^ν − ζ̄₁^ν, ζ₂^ν − ζ̄₂^ν⟩ = 0`: the two differences live in disjoint Dade supports.
    apply ClassFunction.inner_eq_zero_of_disjoint_support
    rw [Set.disjoint_left]
    intro g hg₁ hg₂
    exact Set.disjoint_left.mp H79.dadeSupport_disjoint (hab_supp hg₁) (hcd_supp hg₂)
  · -- `ζ₁^ν 1 = ζ̄₁^ν 1`: the difference vanishes at `1` since `1 ∉ A₁^{τ₁}`.
    have hz : (H79.firstZetaImage - b) (1 : G) = 0 := by
      by_contra h
      exact H79.first.hyp76.hyp71.hyp.one_notMem_dadeSupport
        (hab_supp (ClassFunction.mem_support.mpr h))
    rw [ClassFunction.sub_apply] at hz
    exact sub_eq_zero.mp hz
  · -- `ζ₂^ν 1 = ζ̄₂^ν 1`, symmetrically.
    have hz : (H79.secondZetaImage - d) (1 : G) = 0 := by
      by_contra h
      exact H79.second.hyp76.hyp71.hyp.one_notMem_dadeSupport
        (hcd_supp (ClassFunction.mem_support.mpr h))
    rw [ClassFunction.sub_apply] at hz
    exact sub_eq_zero.mp hz

end Hypothesis79

end OddOrder.Peterfalvi.S09
