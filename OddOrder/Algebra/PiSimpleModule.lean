/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.Ring.Pi
import Mathlib.RingTheory.SimpleModule.Basic

/-!
# A simple module over a finite product of rings lives on one factor

The uniqueness half of Artin–Wedderburn needs to know that the simple modules of
`R = ∏_{i ∈ ι} R_i` are exactly the simple modules of the factors.  The mechanism is the family
of central idempotents `e_i = Pi.single i 1`: they are orthogonal and sum to `1`, so on a simple
module exactly one of them acts as the identity and the rest act as zero.  The whole action then
factors through that single factor.

## Main results

* `OddOrder.PiModule.exists_unique_idem_smul_eq_self` — exactly one `e_i` acts as the identity
* `OddOrder.PiModule.smul_eq_single_smul` — the action then factors through the `i`-th factor
-/

namespace OddOrder.PiModule

section Idem

variable {ι : Type*} [DecidableEq ι] {R : ι → Type*} [∀ i, Ring (R i)]

variable (R) in
/-- The `i`-th central idempotent of a product of rings. -/
def idem (i : ι) : ∀ j, R j := Pi.single i 1

theorem idem_mul (i : ι) (r : ∀ j, R j) : idem R i * r = Pi.single i (r i) := by
  funext j
  by_cases h : i = j
  · subst h; simp [idem]
  · simp [idem, h]

theorem mul_idem (i : ι) (r : ∀ j, R j) : r * idem R i = Pi.single i (r i) := by
  funext j
  by_cases h : i = j
  · subst h; simp [idem]
  · simp [idem, h]

theorem commute_idem (i : ι) (r : ∀ j, R j) : idem R i * r = r * idem R i := by
  rw [idem_mul, mul_idem]

@[simp]
theorem idem_mul_idem_self (i : ι) : idem R i * idem R i = idem R i := by
  rw [idem_mul]; simp [idem]

theorem idem_mul_idem_of_ne {i j : ι} (h : i ≠ j) : idem R i * idem R j = 0 := by
  rw [idem_mul]; simp [idem, Pi.single_eq_of_ne h]

theorem sum_idem [Fintype ι] : ∑ i : ι, idem R i = 1 := by
  funext j
  simp [idem, Finset.sum_apply]

end Idem

section Module

variable {ι : Type*} [DecidableEq ι] {R : ι → Type*} [∀ i, Ring (R i)]
  {M : Type*} [AddCommGroup M] [Module (∀ j, R j) M]

variable (R M) in
/-- Multiplication by the `i`-th central idempotent, as a linear map. -/
def smulIdem (i : ι) : M →ₗ[∀ j, R j] M where
  toFun s := idem R i • s
  map_add' _ _ := smul_add _ _ _
  map_smul' r s := by simp only [RingHom.id_apply, smul_smul, commute_idem i r]

@[simp]
theorem smulIdem_apply (i : ι) (s : M) : smulIdem R M i s = idem R i • s := rfl

/-- Once `e_i` acts as the identity, the whole action factors through the `i`-th factor. -/
theorem smul_eq_single_smul {i : ι} (hi : ∀ s : M, idem R i • s = s) (r : ∀ j, R j) (s : M) :
    r • s = (Pi.single i (r i) : ∀ j, R j) • s := by
  rw [← idem_mul, mul_smul, hi]

/-- **On a simple module over a finite product of rings, exactly one of the central idempotents
acts as the identity** (and the others act as zero). -/
theorem exists_unique_idem_smul_eq_self [Finite ι] [IsSimpleModule (∀ j, R j) M] :
    ∃! i : ι, ∀ s : M, idem R i • s = s := by
  haveI : Fintype ι := Fintype.ofFinite ι
  haveI := IsSimpleModule.nontrivial (∀ j, R j) M
  obtain ⟨s, hs⟩ := exists_ne (0 : M)
  -- some idempotent does not kill `s`
  have hsum : ∑ i : ι, idem R i • s = s := by
    rw [← Finset.sum_smul, sum_idem, one_smul]
  obtain ⟨i, -, hi⟩ : ∃ i ∈ Finset.univ, idem R i • s ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hs (hsum.symm.trans (Finset.sum_eq_zero fun i hi => hcon i hi))
  -- hence its range is everything, and so it acts as the identity
  have hid : ∀ t : M, idem R i • t = t := by
    have hrange : LinearMap.range (smulIdem R M i) = ⊤ := by
      rcases eq_bot_or_eq_top (LinearMap.range (smulIdem R M i)) with h | h
      · refine absurd ?_ hi
        have h0 : smulIdem R M i = 0 := LinearMap.range_eq_bot.mp h
        calc idem R i • s = smulIdem R M i s := rfl
          _ = 0 := by rw [h0]; simp
      · exact h
    intro t
    obtain ⟨u, hu⟩ := (LinearMap.range_eq_top.mp hrange) t
    rw [← hu, smulIdem_apply, smul_smul, idem_mul_idem_self]
  refine ⟨i, hid, fun j hj => ?_⟩
  by_contra hne
  have hzero : idem R j • s = 0 := by
    rw [← hid s, smul_smul, idem_mul_idem_of_ne hne, zero_smul]
  exact hs ((hj s).symm.trans hzero)

end Module

end OddOrder.PiModule
