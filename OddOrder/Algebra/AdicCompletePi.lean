/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.RingTheory.AdicCompletion.Basic

/-!
# Adic completeness of a finite product

`IsAdicComplete I R` transfers to `ι → R` for finite `ι`: everything is componentwise, because
`I ^ n • ⊤` in `ι → R` is exactly the set of tuples with all entries in `I ^ n`.  mathlib has the
transfer along ring isomorphisms (`IsAdicComplete.congr_ringEquiv`) and the change-of-scalars
statement (`IsAdicComplete.map_algebraMap_iff`), but no product instance.

This is the missing link for block idempotents over a `p`-modular system.  For `𝒪` complete,
`Z(𝒪G)` is free over `𝒪` on the class sums, so it is `𝔪`-adically complete, hence `𝔪·Z(𝒪G)` is a
Henselian ideal and idempotents lift along `Z(𝒪G) ↠ Z(FG)`
(`OddOrder.exists_isIdempotentElem_sub_mem`).

Finiteness of `ι` is passed as an *explicit* hypothesis rather than an instance: it is genuinely
needed (an infinite product is not adically complete) but does not occur in the statements, so as
an instance it would be reported as unused.

## Main results

* `OddOrder.mem_pow_smul_top_self_iff`
* `OddOrder.mem_pow_smul_top_pi_iff`
* `OddOrder.isAdicComplete_pi`
-/

namespace OddOrder

variable {R : Type*} [CommRing R] (I : Ideal R) {ι : Type*}

/-- For the ring itself, `I ^ n • ⊤` is just `I ^ n`. -/
theorem mem_pow_smul_top_self_iff {n : ℕ} (r : R) :
    r ∈ (I ^ n • ⊤ : Submodule R R) ↔ r ∈ I ^ n := by
  constructor
  · intro h
    exact Submodule.smul_induction_on h (fun a ha b _ => Ideal.mul_mem_right _ _ ha)
      (fun a b ha hb => Ideal.add_mem _ ha hb)
  · intro h
    have hr : r = r • (1 : R) := by simp
    rw [hr]
    exact Submodule.smul_mem_smul h Submodule.mem_top

/-- In a finite product, `I ^ n • ⊤` is the set of tuples with all entries in `I ^ n`. -/
theorem mem_pow_smul_top_pi_iff (hι : Finite ι) {n : ℕ} (x : ι → R) :
    x ∈ (I ^ n • ⊤ : Submodule R (ι → R)) ↔ ∀ i, x i ∈ I ^ n := by
  classical
  haveI := hι
  haveI : Fintype ι := Fintype.ofFinite ι
  constructor
  · intro hx
    refine Submodule.smul_induction_on hx (fun r hr m _ i => ?_) (fun a b ha hb i => ?_)
    · exact Ideal.mul_mem_right _ _ hr
    · exact Ideal.add_mem _ (ha i) (hb i)
  · intro hx
    have hsum : x = ∑ i : ι, x i • (Pi.single i 1 : ι → R) := by
      funext j
      simp [Pi.single_apply, Finset.sum_ite_eq]
    rw [hsum]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (hx i) Submodule.mem_top

/-- Being Hausdorff is a componentwise condition. -/
theorem isHausdorff_pi (hι : Finite ι) [IsHausdorff I R] : IsHausdorff I (ι → R) where
  haus' x hx := by
    funext i
    refine IsHausdorff.haus' (I := I) (x i) fun n => ?_
    have hn := hx n
    rw [SModEq.sub_mem, sub_zero, mem_pow_smul_top_pi_iff I hι] at hn
    rw [SModEq.sub_mem, sub_zero, mem_pow_smul_top_self_iff]
    exact hn i

/-- Being precomplete is a componentwise condition. -/
theorem isPrecomplete_pi (hι : Finite ι) [IsPrecomplete I R] : IsPrecomplete I (ι → R) where
  prec' f hf := by
    have hcomp : ∀ i : ι, ∃ L : R, ∀ n, (f n i) ≡ L [SMOD (I ^ n • ⊤ : Submodule R R)] := by
      intro i
      refine IsPrecomplete.prec' (I := I) (fun n => f n i) fun {m n} hmn => ?_
      have hmn' := hf hmn
      rw [SModEq.sub_mem, mem_pow_smul_top_pi_iff I hι] at hmn'
      rw [SModEq.sub_mem, mem_pow_smul_top_self_iff]
      exact hmn' i
    choose L hL using hcomp
    refine ⟨L, fun n => ?_⟩
    rw [SModEq.sub_mem, mem_pow_smul_top_pi_iff I hι]
    intro i
    have hi := hL i n
    rw [SModEq.sub_mem, mem_pow_smul_top_self_iff] at hi
    exact hi

/-- **A finite product of a complete ring is complete.** -/
theorem isAdicComplete_pi (hι : Finite ι) [IsAdicComplete I R] : IsAdicComplete I (ι → R) where
  toIsHausdorff := isHausdorff_pi I hι
  toIsPrecomplete := isPrecomplete_pi I hι

end OddOrder
