/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.LinearAlgebra.Dimension.Constructions
import OddOrder.GroupTheory.RepresentationTheory.Modular.CommutatorQuotient
import OddOrder.GroupTheory.RepresentationTheory.Modular.PRegularRadical

/-!
# The `p`-regular classes span `kG ⧸ T'`

Every group element is congruent, modulo the `p`-radical `T'` of the commutator span, to the
chosen representative of the conjugacy class of its `p'`-part (`PRegularRadical`).  Hence
`kG ⧸ T'` is spanned by as many elements as there are `p`-regular classes.

This is the upper bound in Brauer's count; the matching lower bound comes from the semilinear
Frobenius on `kG ⧸ [kG, kG]`.

## Main results

* `OddOrder.RepresentationTheory.Modular.span_range_mkQ_pRegular_eq_top`
* `OddOrder.RepresentationTheory.Modular.finrank_quotient_commutatorRadical_le`
-/

namespace OddOrder.RepresentationTheory.Modular

open MonoidAlgebra OddOrder.GroupTheory

variable {k G : Type*} [Field k] [Group G] [Finite G] {p : ℕ}
  (hp : p.Prime) (hchar : (p : MonoidAlgebra k G) = 0)

/-- Modulo the `p`-radical, every group element is congruent to the chosen representative of the
conjugacy class of its `p'`-part. -/
theorem mkQ_single_eq_mkQ_single_pRegular (g : G) :
    (OddOrder.commutatorRadical (k := k) hp hchar).mkQ (single g (1 : k))
      = (OddOrder.commutatorRadical (k := k) hp hchar).mkQ
          (single (ConjClasses.mk (pRegularPart p g)).out 1) := by
  have hle : commutatorSubmodule k G ≤ OddOrder.commutatorRadical (k := k) hp hchar := by
    rw [commutatorSubmodule_eq_commutatorSpan]
    exact OddOrder.commutatorSpan_le_commutatorRadical hp hchar
  have h1 : (OddOrder.commutatorRadical (k := k) hp hchar).mkQ (single g (1 : k))
      = (OddOrder.commutatorRadical (k := k) hp hchar).mkQ (single (pRegularPart p g) 1) :=
    (Submodule.Quotient.eq _).mpr
      (single_sub_single_pRegularPart_mem hp hchar (isOfFinOrder_of_finite g))
  have h2 : (OddOrder.commutatorRadical (k := k) hp hchar).mkQ (single (pRegularPart p g) (1 : k))
      = (OddOrder.commutatorRadical (k := k) hp hchar).mkQ
          (single (ConjClasses.mk (pRegularPart p g)).out 1) :=
    (Submodule.Quotient.eq _).mpr (hle ((Submodule.Quotient.eq _).mp
      (mkQ_single_eq_mkQ_single_out (k := k) (pRegularPart p g))))
  rw [h1, h2]

/-- Every element of `kG` maps into the span of the `p`-regular class representatives. -/
theorem mkQ_mem_span_range_pRegular (x : MonoidAlgebra k G) :
    (OddOrder.commutatorRadical (k := k) hp hchar).mkQ x
      ∈ Submodule.span k (Set.range fun C : {C : ConjClasses G // IsPRegularClass p C} =>
        (OddOrder.commutatorRadical (k := k) hp hchar).mkQ
          (single (C : ConjClasses G).out 1)) := by
  induction x using MonoidAlgebra.induction_on with
  | hM a =>
    rw [MonoidAlgebra.of_apply, mkQ_single_eq_mkQ_single_pRegular hp hchar a]
    refine Submodule.subset_span ⟨⟨ConjClasses.mk (pRegularPart p a), ?_⟩, rfl⟩
    exact isPRegularClass_mk.mpr (isPRegular_pRegularPart hp (isOfFinOrder_of_finite a))
  | hadd x y hx hy =>
    rw [map_add]
    exact Submodule.add_mem _ hx hy
  | hsmul c x hx =>
    rw [map_smul]
    exact Submodule.smul_mem _ _ hx

/-- **The `p`-regular classes span `kG ⧸ T'`.** -/
theorem span_range_mkQ_pRegular_eq_top :
    Submodule.span k (Set.range fun C : {C : ConjClasses G // IsPRegularClass p C} =>
      (OddOrder.commutatorRadical (k := k) hp hchar).mkQ
        (single (C : ConjClasses G).out 1)) = ⊤ := by
  refine eq_top_iff.mpr fun q _ => ?_
  obtain ⟨x, rfl⟩ := (OddOrder.commutatorRadical (k := k) hp hchar).mkQ_surjective q
  exact mkQ_mem_span_range_pRegular hp hchar x

/-- **Upper bound**: `dim (kG ⧸ T')` is at most the number of `p`-regular classes. -/
theorem finrank_quotient_commutatorRadical_le :
    Module.finrank k (MonoidAlgebra k G ⧸ OddOrder.commutatorRadical (k := k) hp hchar)
      ≤ Nat.card {C : ConjClasses G // IsPRegularClass p C} := by
  classical
  have _ : Fintype {C : ConjClasses G // IsPRegularClass p C} := Fintype.ofFinite _
  have h := finrank_range_le_card (R := k)
    (fun C : {C : ConjClasses G // IsPRegularClass p C} =>
      (OddOrder.commutatorRadical (k := k) hp hchar).mkQ (single (C : ConjClasses G).out 1))
  rw [Set.finrank, span_range_mkQ_pRegular_eq_top hp hchar, finrank_top] at h
  simpa [Nat.card_eq_fintype_card] using h

/-! ### The Frobenius sends a class to the class of its `p'`-part -/

omit [Finite G] in
theorem iterate_frobQuotient_mk_single {m : ℕ}
    (hm : ∀ g : G, g ^ p ^ m = pRegularPart p g) (g : G) :
    (OddOrder.frobQuotient hp hchar)^[m]
        (Submodule.Quotient.mk (single g (1 : k)) :
          MonoidAlgebra k G ⧸ OddOrder.commutatorSpan k (MonoidAlgebra k G))
      = Submodule.Quotient.mk (single (pRegularPart p g) 1) := by
  rw [OddOrder.iterate_frobQuotient_mk, single_pow, one_pow, hm g]

/-- The image of the iterated Frobenius contains every `p`-regular class. -/
theorem mk_single_mem_range_iterate_frobQuotient {m : ℕ}
    (hm : ∀ g : G, g ^ p ^ m = pRegularPart p g) {h : G} (hh : IsPRegular p h) :
    (Submodule.Quotient.mk (single h (1 : k)) :
        MonoidAlgebra k G ⧸ OddOrder.commutatorSpan k (MonoidAlgebra k G))
      ∈ Set.range (OddOrder.frobQuotient hp hchar)^[m] := by
  refine ⟨Submodule.Quotient.mk (single h (1 : k)), ?_⟩
  rw [iterate_frobQuotient_mk_single hp hchar hm h,
    pRegularPart_eq_self_of_isPRegular hp hh]

end OddOrder.RepresentationTheory.Modular
