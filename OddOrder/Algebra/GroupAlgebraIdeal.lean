/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.RingTheory.Ideal.Maps
import OddOrder.GroupTheory.RepresentationTheory.Modular.CenterReduction
import OddOrder.Mathlib.MonoidAlgebra

/-!
# The extended ideal `I·R[G]`

`OddOrder.mem_centerIdeal_iff_mapRingHom_eq_zero` identifies the kernel of coefficient reduction
on the **centre** of a group algebra with the extended ideal `I·Z(RG)`.  Navarro (5.4) is applied
in the whole group algebra, not just its centre, so the same identification is needed there — and
it is easier, because the basis is `G` itself instead of the class sums.

## Main results

* `OddOrder.GroupAlgebra.sum_single_coeff` — `x = ∑_g single g (x.coeff g)`
* `OddOrder.GroupAlgebra.mem_groupAlgebraIdeal_iff_mapRingHom_eq_zero` — `I·R[G]` is the kernel
  of coefficient reduction
-/

namespace OddOrder.GroupAlgebra

variable {R G : Type*} [CommRing R] [Fintype G]

/-- Expansion of an element of `R[G]` on the group basis. -/
theorem sum_single_coeff (x : MonoidAlgebra R G) :
    ∑ g : G, MonoidAlgebra.single g (x.coeff g) = x := by
  classical
  refine MonoidAlgebra.ext (Finsupp.ext fun n => ?_)
  rw [MonoidAlgebra.coeff_finsetSum]
  have hterm : ∀ g : G, (MonoidAlgebra.single g (x.coeff g)).coeff n
      = if g = n then x.coeff g else 0 := by
    intro g
    rw [MonoidAlgebra.coeff_single, Finsupp.single_apply]
  rw [Finset.sum_congr rfl fun g _ => hterm g,
    Finset.sum_ite_eq' Finset.univ n (fun g : G => x.coeff g)]
  simp

variable [Group G]

/-- The extended ideal `I·R[G]`. -/
noncomputable abbrev groupAlgebraIdeal (I : Ideal R) : Ideal (MonoidAlgebra R G) :=
  I.map (algebraMap R (MonoidAlgebra R G))

variable {F : Type*} [CommRing F] (I : Ideal R) (φ : R →+* F)

set_option linter.unusedFintypeInType false in
/-- **The extended ideal is the kernel of coefficient reduction.**  One inclusion is that `I`
reduces to `0`; the other is the expansion on the group basis, whose coefficients must lie
in `I`. -/
theorem mem_groupAlgebraIdeal_iff_mapRingHom_eq_zero (hker : RingHom.ker φ = I)
    (x : MonoidAlgebra R G) :
    x ∈ groupAlgebraIdeal (G := G) I ↔ MonoidAlgebra.mapRingHom G φ x = 0 := by
  classical
  constructor
  · intro hx
    have hle : groupAlgebraIdeal (G := G) I
        ≤ RingHom.ker (MonoidAlgebra.mapRingHom G φ) := by
      rw [Ideal.map_le_iff_le_comap]
      intro a ha
      simp only [Ideal.mem_comap, RingHom.mem_ker]
      have hval : (algebraMap R (MonoidAlgebra R G) a) = a • (1 : MonoidAlgebra R G) := by
        rw [Algebra.algebraMap_eq_smul_one]
      have haz : φ a = 0 := RingHom.mem_ker.mp (by rw [hker]; exact ha)
      rw [hval, OddOrder.GroupTheory.CenterClassSum.mapRingHom_smul, haz, zero_smul]
    exact RingHom.mem_ker.mp (hle hx)
  · intro hx
    have hcoeff : ∀ g : G, x.coeff g ∈ I := by
      intro g
      rw [← hker, RingHom.mem_ker, ← MonoidAlgebra.coeff_mapRingHom, hx]
      rfl
    rw [← sum_single_coeff x]
    refine Submodule.sum_mem _ fun g _ => ?_
    have hsingle : (MonoidAlgebra.single g (x.coeff g) : MonoidAlgebra R G)
        = MonoidAlgebra.single g 1 * algebraMap R (MonoidAlgebra R G) (x.coeff g) := by
      rw [Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one, MonoidAlgebra.smul_single,
        smul_eq_mul, mul_one]
    rw [hsingle]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (hcoeff g))

end OddOrder.GroupAlgebra
