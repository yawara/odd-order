/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.LinearAlgebra.Dimension.Constructions
import OddOrder.GroupTheory.RepresentationTheory.Modular.CommutatorQuotient
import OddOrder.GroupTheory.RepresentationTheory.Modular.PRegularRadical

/-!
# The `p`-regular classes are a basis of `kG ⧸ T'`

Every group element is congruent, modulo the `p`-radical `T'` of the commutator span, to the
chosen representative of the conjugacy class of its `p'`-part (`PRegularRadical`).  Hence
`kG ⧸ T'` is spanned by as many elements as there are `p`-regular classes.

Those spanning vectors are moreover independent: an element of `T'` is killed by some iterate of
the semilinear Frobenius on `kG ⧸ [kG, kG]`, and after inflating the number of iterations to a
multiple of the uniform exponent that iterate *fixes* every `p`-regular class while raising the
coefficients to a `p`-power.  So a relation among the `p`-regular classes modulo `T'` becomes a
relation among the conjugacy classes modulo `[kG, kG]`, where they are independent.

`dim_k (kG ⧸ T')` is therefore exactly the number of `p`-regular classes.  This is one of the two
halves of Brauer's count of the irreducible modular representations; the other half identifies
`T'` with `J(kG) + [kG, kG]`.

## Main results

* `OddOrder.RepresentationTheory.Modular.span_range_mkQ_pRegular_eq_top`
* `OddOrder.RepresentationTheory.Modular.finrank_quotient_commutatorRadical_le`
* `OddOrder.RepresentationTheory.Modular.linearIndependent_mkQ_pRegular`
* `OddOrder.RepresentationTheory.Modular.basisPRegularQuotient`
* `OddOrder.RepresentationTheory.Modular.finrank_quotient_commutatorRadical`
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
  | of a =>
    rw [MonoidAlgebra.of_apply, mkQ_single_eq_mkQ_single_pRegular hp hchar a]
    refine Submodule.subset_span ⟨⟨ConjClasses.mk (pRegularPart p a), ?_⟩, rfl⟩
    exact isPRegularClass_mk.mpr (isPRegular_pRegularPart hp (isOfFinOrder_of_finite a))
  | add x y hx hy =>
    rw [map_add]
    exact Submodule.add_mem _ hx hy
  | smul c x hx =>
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

omit [Finite G] in
/-- The image of the iterated Frobenius contains every `p`-regular class. -/
theorem mk_single_mem_range_iterate_frobQuotient {m : ℕ}
    (hm : ∀ g : G, g ^ p ^ m = pRegularPart p g) {h : G} (hh : IsPRegular p h) :
    (Submodule.Quotient.mk (single h (1 : k)) :
        MonoidAlgebra k G ⧸ OddOrder.commutatorSpan k (MonoidAlgebra k G))
      ∈ Set.range (OddOrder.frobQuotient hp hchar)^[m] := by
  refine ⟨Submodule.Quotient.mk (single h (1 : k)), ?_⟩
  rw [iterate_frobQuotient_mk_single hp hchar hm h,
    pRegularPart_eq_self_of_isPRegular hp hh]

variable (p) in
/-- The span of the `p`-regular classes inside `kG ⧸ [kG, kG]`. -/
noncomputable def pRegularClassSpan :
    Submodule k (MonoidAlgebra k G ⧸ OddOrder.commutatorSpan k (MonoidAlgebra k G)) :=
  Submodule.span k {u | ∃ h : G, IsPRegular p h ∧
    u = Submodule.Quotient.mk (single h (1 : k))}

omit [Finite G] in
theorem mk_single_mem_pRegularClassSpan {h : G} (hh : IsPRegular p h) :
    (Submodule.Quotient.mk (single h (1 : k)) :
      MonoidAlgebra k G ⧸ OddOrder.commutatorSpan k (MonoidAlgebra k G))
      ∈ pRegularClassSpan (k := k) (G := G) p :=
  Submodule.subset_span ⟨h, hh, rfl⟩

/-- **The image of the iterated Frobenius lands in the span of the `p`-regular classes.**
Bilinear reduction to group elements, where the Frobenius literally takes the `p'`-part. -/
theorem iterate_frobQuotient_mem_pRegularClassSpan {m : ℕ}
    (hm : ∀ g : G, g ^ p ^ m = pRegularPart p g)
    (u : MonoidAlgebra k G ⧸ OddOrder.commutatorSpan k (MonoidAlgebra k G)) :
    (OddOrder.frobQuotient hp hchar)^[m] u ∈ pRegularClassSpan (k := k) (G := G) p := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ u
  induction x using MonoidAlgebra.induction_on with
  | of a =>
    rw [MonoidAlgebra.of_apply, iterate_frobQuotient_mk_single hp hchar hm]
    exact mk_single_mem_pRegularClassSpan
      (isPRegular_pRegularPart hp (isOfFinOrder_of_finite a))
  | add x y hx hy =>
    rw [Submodule.Quotient.mk_add, OddOrder.iterate_frobQuotient_add]
    exact Submodule.add_mem _ hx hy
  | smul c x hx =>
    rw [Submodule.Quotient.mk_smul, OddOrder.iterate_frobQuotient_smul]
    exact Submodule.smul_mem _ _ hx

/-! ### The `p`-regular classes are a basis of `kG ⧸ T'`

The lower bound matching `finrank_quotient_commutatorRadical_le`.  If a combination of
`p`-regular class representatives lies in the `p`-radical `T'`, some iterate of the Frobenius
kills its class in `kG ⧸ [kG, kG]`.  Inflating the number of iterations to a *multiple* of the
uniform exponent makes that iterate fix each `p`-regular class while raising each coefficient to
a `p`-power, so the independence of the conjugacy classes in `kG ⧸ [kG, kG]`
(`linearIndependent_mkQ_out`) forces every coefficient to vanish.
-/

omit [Finite G] in
/-- Being fixed by `x ↦ x ^ p ^ m` propagates to every multiple of `m`. -/
theorem pow_prime_pow_mul_eq_self {m : ℕ} {h : G} (hfix : h ^ p ^ m = h) (t : ℕ) :
    h ^ p ^ (t * m) = h := by
  induction t with
  | zero => simp
  | succ t ih => rw [Nat.succ_mul, pow_add, pow_mul, ih, hfix]

omit [Finite G] in
/-- The iterated Frobenius **fixes** the class of a `p`-regular element as soon as the number of
iterations is a multiple of the uniform exponent. -/
theorem iterate_frobQuotient_mk_single_of_isPRegular {m : ℕ}
    (hm : ∀ g : G, g ^ p ^ m = pRegularPart p g) {h : G} (hh : IsPRegular p h) (t : ℕ) :
    (OddOrder.frobQuotient hp hchar)^[t * m]
        (Submodule.Quotient.mk (single h (1 : k)) :
          MonoidAlgebra k G ⧸ OddOrder.commutatorSpan k (MonoidAlgebra k G))
      = Submodule.Quotient.mk (single h 1) := by
  have hfix : h ^ p ^ m = h := by
    rw [hm h, pRegularPart_eq_self_of_isPRegular hp hh]
  rw [OddOrder.iterate_frobQuotient_mk, single_pow, one_pow, pow_prime_pow_mul_eq_self hfix t]

/-- **A combination of `p`-regular classes lying in the `p`-radical is trivial.**  This is the
heart of the lower bound: iterate the Frobenius `j · m` times, where the `p ^ j`-th power already
lands in `[kG, kG]` and `m` is the uniform exponent, so that the iterate is simultaneously zero
and the identity on the `p`-regular classes. -/
theorem eq_zero_of_sum_smul_mem_commutatorRadical
    [Fintype {C : ConjClasses G // IsPRegularClass p C}]
    (c : {C : ConjClasses G // IsPRegularClass p C} → k)
    (hmem : ∑ D, c D • single (D : ConjClasses G).out (1 : k)
      ∈ OddOrder.commutatorRadical (k := k) hp hchar) (C) : c C = 0 := by
  classical
  have : Fintype G := Fintype.ofFinite G
  obtain ⟨m, hmpos, hm⟩ := exists_uniform_pow_prime_pow_eq_pRegularPart (G := G) hp
  obtain ⟨j, hj⟩ := (OddOrder.mem_commutatorRadical_iff hp hchar).mp hmem
  -- the class of the combination in `kG ⧸ [kG, kG]`
  have hmk : (Submodule.Quotient.mk (∑ D, c D • single (D : ConjClasses G).out (1 : k)) :
        MonoidAlgebra k G ⧸ OddOrder.commutatorSpan k (MonoidAlgebra k G))
      = ∑ D, c D • (Submodule.Quotient.mk (single (D : ConjClasses G).out (1 : k)) :
          MonoidAlgebra k G ⧸ OddOrder.commutatorSpan k (MonoidAlgebra k G)) := by
    rw [← Submodule.mkQ_apply, map_sum]
    simp only [map_smul, Submodule.mkQ_apply]
  -- some iterate of the Frobenius kills it, hence so does every later one
  have hzero : ∀ n, j ≤ n → (OddOrder.frobQuotient hp hchar)^[n]
      (Submodule.Quotient.mk (∑ D, c D • single (D : ConjClasses G).out (1 : k)) :
        MonoidAlgebra k G ⧸ OddOrder.commutatorSpan k (MonoidAlgebra k G)) = 0 := by
    intro n hn
    have hj0 : (OddOrder.frobQuotient hp hchar)^[j]
        (Submodule.Quotient.mk (∑ D, c D • single (D : ConjClasses G).out (1 : k)) :
          MonoidAlgebra k G ⧸ OddOrder.commutatorSpan k (MonoidAlgebra k G)) = 0 := by
      rw [OddOrder.iterate_frobQuotient_mk]
      exact (Submodule.Quotient.mk_eq_zero _).mpr hj
    rw [show n = (n - j) + j by omega, Function.iterate_add_apply, hj0,
      OddOrder.iterate_frobQuotient_zero]
  -- `j · m` iterations: the classes are fixed, the coefficients get raised to `p ^ (j · m)`
  have hfrob : ∑ D, (c D) ^ p ^ (j * m) •
      (Submodule.Quotient.mk (single (D : ConjClasses G).out (1 : k)) :
        MonoidAlgebra k G ⧸ OddOrder.commutatorSpan k (MonoidAlgebra k G)) = 0 := by
    rw [← hzero (j * m) (Nat.le_mul_of_pos_right j hmpos), hmk,
      OddOrder.iterate_frobQuotient_sum]
    refine Finset.sum_congr rfl fun D _ => ?_
    rw [OddOrder.iterate_frobQuotient_smul,
      iterate_frobQuotient_mk_single_of_isPRegular hp hchar (fun g => (hm g).1)
        (isPRegular_out D.2) j]
  -- independence of the conjugacy classes in `kG ⧸ [kG, kG]`
  have hli : LinearIndependent k fun D : {C : ConjClasses G // IsPRegularClass p C} =>
      (Submodule.Quotient.mk (single (D : ConjClasses G).out (1 : k)) :
        MonoidAlgebra k G ⧸ OddOrder.commutatorSpan k (MonoidAlgebra k G)) :=
    (linearIndependent_mkQ_out (k := k) (G := G)).comp
      (fun D : {C : ConjClasses G // IsPRegularClass p C} => (D : ConjClasses G))
      Subtype.val_injective
  have := Fintype.linearIndependent_iff.mp hli (fun D => (c D) ^ p ^ (j * m)) hfrob C
  exact pow_eq_zero_iff (pow_ne_zero _ hp.pos.ne') |>.mp this

/-- **The `p`-regular classes are linearly independent in `kG ⧸ T'`.** -/
theorem linearIndependent_mkQ_pRegular :
    LinearIndependent k fun C : {C : ConjClasses G // IsPRegularClass p C} =>
      (OddOrder.commutatorRadical (k := k) hp hchar).mkQ
        (single (C : ConjClasses G).out (1 : k)) := by
  classical
  have : Fintype {C : ConjClasses G // IsPRegularClass p C} := Fintype.ofFinite _
  refine Fintype.linearIndependent_iff.mpr fun c hc C => ?_
  refine eq_zero_of_sum_smul_mem_commutatorRadical hp hchar c ?_ C
  have hmk : (OddOrder.commutatorRadical (k := k) hp hchar).mkQ
      (∑ D, c D • single (D : ConjClasses G).out (1 : k)) = 0 := by
    rw [map_sum]
    simp only [map_smul]
    exact hc
  exact (Submodule.Quotient.mk_eq_zero _).mp hmk

/-- **The `p`-regular classes are a basis of `kG ⧸ T'`.** -/
noncomputable def basisPRegularQuotient :
    Module.Basis {C : ConjClasses G // IsPRegularClass p C} k
      (MonoidAlgebra k G ⧸ OddOrder.commutatorRadical (k := k) hp hchar) :=
  Module.Basis.mk (linearIndependent_mkQ_pRegular hp hchar)
    (span_range_mkQ_pRegular_eq_top hp hchar).ge

/-- **`dim_k (kG ⧸ T')` is the number of `p`-regular classes of `G`.**  This is the
linear-algebra half of Brauer's count of the irreducible modular representations; what remains
is to identify `T'` with `J(kG) + [kG, kG]`. -/
theorem finrank_quotient_commutatorRadical :
    Module.finrank k (MonoidAlgebra k G ⧸ OddOrder.commutatorRadical (k := k) hp hchar)
      = Nat.card {C : ConjClasses G // IsPRegularClass p C} := by
  classical
  have : Fintype {C : ConjClasses G // IsPRegularClass p C} := Fintype.ofFinite _
  rw [Module.finrank_eq_card_basis (basisPRegularQuotient hp hchar), Nat.card_eq_fintype_card]

end OddOrder.RepresentationTheory.Modular
