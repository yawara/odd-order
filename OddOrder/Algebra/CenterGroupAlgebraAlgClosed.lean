/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Algebra.AlgClosedIdempotentLift
import OddOrder.Algebra.CenterIdempotentLift

/-!
# Block idempotents over a coefficient ring that splits the ordinary side

`CenterGroupAlgebraHenselian` lifts idempotents to `Z(𝒪G)` from completeness of `𝒪`.  That
hypothesis is incompatible with `K = Frac 𝒪` being a splitting field for `K[G]`: a complete
discretely valued field is never algebraically closed, and conversely the valuation ring of an
algebraically closed complete field has `𝔪² = 𝔪` (issue 9506).

Here the same lifting is obtained from `AlgClosedIdempotentLift` instead, which asks only that `𝒪`
be local and integrally closed with algebraically closed fraction field.  `Z(𝒪G)` is free of finite
rank on the class sums (`centerBasis`), which is all the hypothesis needs.

This is what lets the valuation ring of `ℂ_[p]` — for which the ordinary side splits for free —
carry the block theory.

## Main results

* `OddOrder.existsUnique_isIdempotentElem_centerGroupAlgebra_of_isAlgClosed`
* `OddOrder.existsUnique_isIdempotentElem_mapRingHom_eq_of_isAlgClosed` — the same, phrased for
  the reduction `Z(𝒪G) → Z(FG)`, as the block theory consumes it
-/

namespace OddOrder

open IsLocalRing OddOrder.GroupTheory.CenterClassSum

variable {𝒪 G : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsLocalRing 𝒪] [IsIntegrallyClosed 𝒪]
  [IsAlgClosed (FractionRing 𝒪)] [Group G]

/-- **Idempotents lift uniquely to `Z(𝒪G)`** when the fraction field of `𝒪` is algebraically
closed.  Same conclusion as `existsUnique_isIdempotentElem_centerGroupAlgebra`, with completeness
of `𝒪` traded for `IsAlgClosed (FractionRing 𝒪)`.

Finiteness of `G` is an explicit hypothesis rather than an instance: it is needed only to produce
the class-sum basis, so as an instance it would be reported as unused. -/
theorem existsUnique_isIdempotentElem_centerGroupAlgebra_of_isAlgClosed
    (hG : Finite G) {c : ↥(Subalgebra.center 𝒪 (MonoidAlgebra 𝒪 G))}
    (hc : c * c - c ∈ centerIdeal (G := G) (maximalIdeal 𝒪)) :
    ∃! e : ↥(Subalgebra.center 𝒪 (MonoidAlgebra 𝒪 G)),
      IsIdempotentElem e ∧ e - c ∈ centerIdeal (G := G) (maximalIdeal 𝒪) := by
  classical
  haveI := hG
  haveI : Fintype G := Fintype.ofFinite G
  haveI hfc : Finite (ConjClasses G) := Quotient.finite _
  haveI : Fintype (ConjClasses G) := Fintype.ofFinite _
  haveI : Module.Free 𝒪 ↥(Subalgebra.center 𝒪 (MonoidAlgebra 𝒪 G)) :=
    Module.Free.of_basis centerBasis
  haveI : Module.Finite 𝒪 ↥(Subalgebra.center 𝒪 (MonoidAlgebra 𝒪 G)) :=
    Module.Finite.of_basis centerBasis
  exact existsUnique_isIdempotentElem_sub_mem_of_isAlgClosed hc

-- Same as in `CenterIdempotentLift`: the finiteness instances are consumed through the kernel
-- description of `centerIdeal`.
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- **Idempotents of `Z(FG)` lift uniquely to `Z(𝒪G)`** when the fraction field of `𝒪` is
algebraically closed.  Same conclusion as `existsUnique_isIdempotentElem_mapRingHom_eq`, with
completeness of `𝒪` traded for `IsAlgClosed (FractionRing 𝒪)`; this is the form the block theory
consumes,
producing Navarro's `f_B ∈ Z(𝒪G)` from the block idempotents `e_B ∈ Z(kG)`. -/
theorem existsUnique_isIdempotentElem_mapRingHom_eq_of_isAlgClosed
    {F : Type*} [CommRing F] [Fintype G] [DecidableEq (ConjClasses G)] [Fintype (ConjClasses G)]
    (φ : 𝒪 →+* F) (hφ : Function.Surjective φ) (hker : RingHom.ker φ = maximalIdeal 𝒪)
    (hG : Finite G) {z : MonoidAlgebra F G}
    (hzc : z ∈ Subalgebra.center F (MonoidAlgebra F G)) (hz : z * z = z) :
    ∃! e : ↥(Subalgebra.center 𝒪 (MonoidAlgebra 𝒪 G)),
      IsIdempotentElem e ∧ centerReduceHom φ e = z := by
  classical
  obtain ⟨c, hcmem, hc⟩ := exists_mem_center_mapRingHom_eq (G := G) hφ hzc
  set cc : ↥(Subalgebra.center 𝒪 (MonoidAlgebra 𝒪 G)) := ⟨c, hcmem⟩ with hcc
  have hccred : centerReduceHom φ cc = z := hc
  have happrox : cc * cc - cc ∈ centerIdeal (G := G) (maximalIdeal 𝒪) := by
    rw [mem_centerIdeal_iff_mapRingHom_eq_zero _ φ hker, map_sub, map_mul, hccred, hz, sub_self]
  obtain ⟨e, ⟨he, hec⟩, huniq⟩ :=
    existsUnique_isIdempotentElem_centerGroupAlgebra_of_isAlgClosed (G := G) hG happrox
  refine ⟨e, ⟨he, ?_⟩, fun e' he' => ?_⟩
  · have hzero : centerReduceHom φ (e - cc) = 0 :=
      (mem_centerIdeal_iff_mapRingHom_eq_zero _ φ hker _).mp hec
    rw [map_sub, hccred, sub_eq_zero] at hzero
    exact hzero
  · refine huniq e' ⟨he'.1, ?_⟩
    rw [mem_centerIdeal_iff_mapRingHom_eq_zero _ φ hker, map_sub, he'.2, hccred, sub_self]

end OddOrder
