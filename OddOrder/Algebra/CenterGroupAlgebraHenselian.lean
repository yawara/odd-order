/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Algebra.AdicCompletePi
import OddOrder.Algebra.IdempotentLift
import OddOrder.GroupTheory.RepresentationTheory.CenterClassSumBasis

/-!
# `Z(𝒪G)` is Henselian at `I·Z(𝒪G)`

The centre of a group algebra is free over the coefficient ring on the class sums
(`CenterClassSum.centerBasis`), so for a complete coefficient ring it is adically complete
(`isAdicComplete_of_basis`), hence Henselian at the extended ideal, hence idempotents lift along
`Z(𝒪G) ↠ Z(FG)` (`exists_isIdempotentElem_sub_mem`).

This is what produces Navarro's block idempotents `f_B ∈ Z(𝒪G)`, the elements Brauer's second
main theorem (5.2) is proved with.

⚠ Completeness of `𝒪` is used, not just Henselianness.  For an arbitrary Henselian local `𝒪` the
same conclusion holds — a module-finite algebra over a Henselian local ring is a Henselian pair
(Stacks 09XI) — but that is not in mathlib and deriving it from single-root lifting needs
multivariable Hensel.  The `p`-modular systems built from complete discrete valuation rings
(`ℤ_[p]`, `WittVector p k`) satisfy the hypothesis; the valuation ring of `ℂ_p` does not, since
its value group is divisible and hence `𝔪² = 𝔪`.

Finiteness of `G` is an explicit hypothesis: it is needed for the class-sum basis but does not
occur in the statements, so as an instance it would be reported as unused.

## Main results

* `OddOrder.isAdicComplete_centerGroupAlgebra`
* `OddOrder.henselianRing_centerGroupAlgebra`
* `OddOrder.existsUnique_isIdempotentElem_centerGroupAlgebra`
-/

namespace OddOrder

open OddOrder.GroupTheory.CenterClassSum

variable {𝒪 G : Type*} [CommRing 𝒪] [Group G]
variable (I : Ideal 𝒪) [IsAdicComplete I 𝒪]

/-- The extended ideal `I·Z(𝒪G)`. -/
noncomputable abbrev centerIdeal : Ideal ↥(Subalgebra.center 𝒪 (MonoidAlgebra 𝒪 G)) :=
  I.map (algebraMap 𝒪 ↥(Subalgebra.center 𝒪 (MonoidAlgebra 𝒪 G)))

/-- **`Z(𝒪G)` is `I`-adically complete** when `𝒪` is: it is free on the class sums. -/
theorem isAdicComplete_centerGroupAlgebra (hG : Finite G) :
    IsAdicComplete I ↥(Subalgebra.center 𝒪 (MonoidAlgebra 𝒪 G)) := by
  classical
  have := hG
  have : Fintype G := Fintype.ofFinite G
  have hfc : Finite (ConjClasses G) := Quotient.finite _
  have : Fintype (ConjClasses G) := Fintype.ofFinite _
  exact isAdicComplete_of_basis I hfc centerBasis

/-- **`Z(𝒪G)` is complete for the extended ideal `I·Z(𝒪G)`.** -/
theorem isAdicComplete_centerIdeal (hG : Finite G) :
    IsAdicComplete (centerIdeal (G := G) I) ↥(Subalgebra.center 𝒪 (MonoidAlgebra 𝒪 G)) :=
  (IsAdicComplete.map_algebraMap_iff (I := I)
    (M := ↥(Subalgebra.center 𝒪 (MonoidAlgebra 𝒪 G)))).mpr
    (isAdicComplete_centerGroupAlgebra I hG)

/-- **`I·Z(𝒪G)` is a Henselian ideal.** -/
theorem henselianRing_centerGroupAlgebra (hG : Finite G) :
    HenselianRing ↥(Subalgebra.center 𝒪 (MonoidAlgebra 𝒪 G)) (centerIdeal (G := G) I) := by
  exact @IsAdicComplete.henselianRing _ _ _ (isAdicComplete_centerIdeal (G := G) I hG)

/-- **Idempotents lift uniquely to `Z(𝒪G)`.**  An element of the centre that is idempotent modulo
`I·Z(𝒪G)` differs from a unique genuine idempotent by an element of `I·Z(𝒪G)`. -/
theorem existsUnique_isIdempotentElem_centerGroupAlgebra (hG : Finite G)
    {c : ↥(Subalgebra.center 𝒪 (MonoidAlgebra 𝒪 G))}
    (hc : c * c - c ∈ centerIdeal (G := G) I) :
    ∃! e : ↥(Subalgebra.center 𝒪 (MonoidAlgebra 𝒪 G)),
      IsIdempotentElem e ∧ e - c ∈ centerIdeal (G := G) I := by
  exact @existsUnique_isIdempotentElem_sub_mem _ _ _
    (henselianRing_centerGroupAlgebra (G := G) I hG) _ hc

end OddOrder
