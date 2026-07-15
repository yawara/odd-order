/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.GaloisCharacter
import OddOrder.GroupTheory.RepresentationTheory.InducedCharacter
import OddOrder.Algebra.GaloisRationalInteger

/-!
# Galois transport of virtual-character inner products

The coefficientwise action of a ring automorphism `σ : ℂ ≃+* ℂ` on class functions
(`ClassFunction.mapRingEquiv`) is a `ℤ`-isometry of the virtual-character lattice `ZIrr G`:

* `ClassFunction.inner_mapRingEquiv_eq_of_mem_ZIrr` — `⟨σφ, ση⟩ = ⟨φ, η⟩` for virtual
  characters `φ, η`.  Unlike the general `ClassFunction.mapRingEquiv_inner` (which needs a global
  commutation of `σ` with complex conjugation), no `star`-hypothesis is required: virtual-character
  values satisfy `χ(g⁻¹) = star (χ(g))` (`OddOrder.Algebra.apply_inv_eq_star_of_mem_ZIrr`), and the
  common inner product is a rational integer (`ClassFunction.inner_mem_ZIrr_int`), hence `σ`-fixed.
* `ClassFunction.inner_eq_intCast_of_mapRingEquiv_eq_add` — the **coefficient-constancy engine**
  (Coq `a_aut`, `PFsection11.v`): if the Galois transport moves `φ` only by a correction orthogonal
  to the transported test vector `η' = ση`, then the integral coefficient is unchanged:
  `⟨φ, η⟩ = m ⟹ ⟨φ, η'⟩ = m`.  This is the step that makes the `σ`-grid coefficients of a
  Dade image constant along Galois orbits of the grid (Peterfalvi (3.9.b)-type row/column
  constancy, used by (10.9)/(11.9.a)).

These are the generic halves of the T-side Galois-transport arguments of
`OddOrder.Peterfalvi.S16` (`TGapGalois.lean`), hoisted to a shared leaf so that the `M`-side
(11.9.a) row-projection analysis (Peterfalvi §11, issues 1024/9085) can import them without the
S16 closure; the S16 consumers cite this shared API directly (issue 9085).
-/

namespace OddOrder.RepresentationTheory.ClassFunction

open OddOrder.RepresentationTheory

variable {L : Type*} [Group L]

/-- **`mapRingEquiv` is a `ℤ`-isometry of `ZIrr`**: a coefficient automorphism preserves the inner
product of two virtual characters.  Unlike `ClassFunction.mapRingEquiv_inner`, no global
commutation with complex conjugation is needed: virtual-character values satisfy
`χ(g⁻¹) = star (χ(g))`, and the common inner product is a rational integer. -/
theorem inner_mapRingEquiv_eq_of_mem_ZIrr [Finite L] [Fintype L]
    [Invertible (Nat.card L : ℂ)]
    (σ : ℂ ≃+* ℂ) {φ η : ClassFunction L ℂ}
    (hφ : φ ∈ ZIrr L) (hη : η ∈ ZIrr L) :
    ClassFunction.inner (ClassFunction.mapRingEquiv σ φ)
        (ClassFunction.mapRingEquiv σ η)
      = ClassFunction.inner φ η := by
  have hstar (g : L) :
      star (ClassFunction.mapRingEquiv σ η g) = σ (star (η g)) := by
    rw [← OddOrder.Algebra.apply_inv_eq_star_of_mem_ZIrr
      (ClassFunction.mapRingEquiv_mem_ZIrr σ hη) g,
      ClassFunction.mapRingEquiv_apply,
      OddOrder.Algebra.apply_inv_eq_star_of_mem_ZIrr hη g]
  obtain ⟨m, hm⟩ := ClassFunction.inner_mem_ZIrr_int hφ hη
  have hsum :
      ClassFunction.innerSum (ClassFunction.mapRingEquiv σ φ)
          (ClassFunction.mapRingEquiv σ η)
        = σ (ClassFunction.innerSum φ η) := by
    rw [ClassFunction.innerSum, ClassFunction.innerSum, map_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    change σ (φ g) * star (σ (η g)) = σ (φ g * star (η g))
    have hg := hstar g
    change star (σ (η g)) = σ (star (η g)) at hg
    rw [hg, map_mul]
  calc
    ClassFunction.inner (ClassFunction.mapRingEquiv σ φ)
        (ClassFunction.mapRingEquiv σ η)
        = σ (ClassFunction.inner φ η) := by
      rw [ClassFunction.inner, ClassFunction.inner, hsum]
      have hcoef : σ (⅟(Nat.card L : ℂ)) = ⅟(Nat.card L : ℂ) := by
        simp [invOf_eq_inv, map_inv₀, map_natCast]
      calc
        ⅟(Nat.card L : ℂ) * σ (ClassFunction.innerSum φ η)
            = σ (⅟(Nat.card L : ℂ)) * σ (ClassFunction.innerSum φ η) := by rw [hcoef]
        _ = σ (⅟(Nat.card L : ℂ) * ClassFunction.innerSum φ η) := (map_mul σ _ _).symm
    _ = ClassFunction.inner φ η := by rw [hm]; simp

/-- **The Galois coefficient-constancy engine** (Coq `a_aut`): if a coefficient automorphism moves
`φ` only by a correction orthogonal to the transported test vector `η' = σ(η)`, then the integral
coefficient of `φ` along `η` transports to `η'` unchanged: `⟨φ, η⟩ = m ⟹ ⟨φ, η'⟩ = m`.  This is
the Peterfalvi (3.9.b)-type row/column constancy step of the (10.9)/(11.9.a) grid analyses. -/
theorem inner_eq_intCast_of_mapRingEquiv_eq_add [Fintype L]
    [Invertible (Nat.card L : ℂ)]
    (σ : ℂ ≃+* ℂ)
    {φ η η' correction : ClassFunction L ℂ} (m : ℤ)
    (hφZ : φ ∈ ZIrr L) (hηZ : η ∈ ZIrr L)
    (hφ : ClassFunction.mapRingEquiv σ φ = φ + correction)
    (hη : ClassFunction.mapRingEquiv σ η = η')
    (hm : ClassFunction.inner φ η = (m : ℂ))
    (hcorrection : ClassFunction.inner correction η' = 0) :
    ClassFunction.inner φ η' = (m : ℂ) := by
  have htransport := inner_mapRingEquiv_eq_of_mem_ZIrr σ hφZ hηZ
  rw [hφ, hη, ClassFunction.inner_add_left, hcorrection, add_zero, hm] at htransport
  simpa using htransport

end OddOrder.RepresentationTheory.ClassFunction
