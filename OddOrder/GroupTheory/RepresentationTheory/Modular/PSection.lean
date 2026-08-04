/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.Modular.GeneralizedDecomposition

/-!
# `p`-sections

For a `p`-element `x`, the **`p`-section** of `x` is

`S(x) = {u ∈ G | u_p is G-conjugate to x}`,

a union of conjugacy classes.  Navarro's remark before (5.10) is that `S(x)` is parametrised by
the `p`-regular classes of `C_G(x)`: every element of `S(x)` is conjugate to `x y` for a
`p`-regular `y ∈ C_G(x)`, and conversely.  Both directions are the uniqueness of the `p`/`p'`
factorisation (`eq_pPart_of_commute`).

That is exactly what turns "vanishes on `S(x)`" — the hypothesis of Navarro (5.10) — into
"vanishes at `x y` for every `p`-regular `y ∈ C_G(x)`", which is the form the generalized
decomposition numbers see.

## Main definitions

* `OddOrder.RepresentationTheory.Modular.pSection` — `S(x)`

## Main results

* `OddOrder.RepresentationTheory.Modular.pPart_mul_eq_of_isPElement` — `(xy)_p = x`
* `OddOrder.RepresentationTheory.Modular.mem_pSection_iff` — the parametrisation of `S(x)`
* `OddOrder.RepresentationTheory.Modular.forall_pSection_iff` — vanishing on `S(x)`, restated
-/

namespace OddOrder.RepresentationTheory.Modular

open OddOrder.GroupTheory

section PPart

variable {p : ℕ} {G : Type*} [Group G]

/-- **`(xy)_p = x`** when `x` is a `p`-element, `y` is `p`-regular and the two commute.  This is
what makes `C_G((xy)_p) = C_G(x)`, the hypothesis under which Navarro (5.7) applies. -/
theorem pPart_mul_eq_of_isPElement (hp : p.Prime) {x y : G} (hcomm : Commute x y)
    (hx : IsPElement p x) (hy : IsPRegular p y) : pPart p (x * y) = x :=
  (eq_pPart_of_commute hp hcomm hx hy hcomm.eq.symm).1.symm

/-- The `p'`-part of `x y` is `y`, in the same situation. -/
theorem pRegularPart_mul_eq_of_isPElement (hp : p.Prime) {x y : G} (hcomm : Commute x y)
    (hx : IsPElement p x) (hy : IsPRegular p y) : pRegularPart p (x * y) = y :=
  (eq_pPart_of_commute hp hcomm hx hy hcomm.eq.symm).2.symm

/-- **`p`-regularity does not see the ambient group.** -/
theorem isPRegular_coe_iff {H : Subgroup G} {y : ↥H} :
    IsPRegular p ((y : G)) ↔ IsPRegular p y := by
  rw [IsPRegular, IsPRegular, Subgroup.orderOf_coe]

/-- **A `p`-regular element of a subgroup is `p`-regular in the ambient group.** -/
theorem isPRegular_coe {H : Subgroup G} {y : ↥H} (hy : IsPRegular p y) :
    IsPRegular p ((y : G)) := isPRegular_coe_iff.mpr hy

end PPart

section PSection

variable {p : ℕ} {G : Type*} [Group G] [Finite G]

/-- **The `p`-section of `x`**: the elements whose `p`-part is conjugate to `x`. -/
def pSection (p : ℕ) (x : G) : Set G := {u | IsConj (pPart p u) x}

omit [Finite G] in
theorem mem_pSection_iff_isConj_pPart {x u : G} : u ∈ pSection p x ↔ IsConj (pPart p u) x :=
  Iff.rfl

omit [Finite G] in
/-- `x y` lies in the `p`-section of `x`. -/
theorem mul_mem_pSection (hp : p.Prime) {x y : G} (hcomm : Commute x y) (hx : IsPElement p x)
    (hy : IsPRegular p y) : x * y ∈ pSection p x := by
  rw [mem_pSection_iff_isConj_pPart, pPart_mul_eq_of_isPElement hp hcomm hx hy]

/-- **The `p`-section is parametrised by the `p`-regular elements of `C_G(x)`.**  Every element of
`S(x)` is conjugate to `x y` for a `p`-regular `y ∈ C_G(x)`, and conversely. -/
theorem mem_pSection_iff (hp : p.Prime) {x : G} (hx : IsPElement p x) {u : G} :
    u ∈ pSection p x ↔
      ∃ y : G, y ∈ centralizerOf x ∧ IsPRegular p y ∧ IsConj u (x * y) := by
  constructor
  · intro hu
    -- move `u` by the conjugator that takes its `p`-part to `x`
    obtain ⟨c, hc⟩ := isConj_iff.mp hu
    set w : G := c * u * c⁻¹ with hw
    have hwp : pPart p w = x := by rw [hw, pPart_conj, hc]
    refine ⟨pRegularPart p w, ?_, isPRegular_pRegularPart hp (isOfFinOrder_of_finite w), ?_⟩
    · refine Subgroup.mem_centralizer_iff.mpr ?_
      rintro z rfl
      rw [← hwp]
      exact (commute_pRegularPart_pPart w).symm
    · refine isConj_iff.mpr ⟨c, ?_⟩
      rw [← hw, ← hwp]
      exact (pPart_mul_pRegularPart hp (isOfFinOrder_of_finite w)).symm
  · rintro ⟨y, hy, hyreg, hconj⟩
    have hcomm : Commute x y := (Subgroup.mem_centralizer_iff.mp hy) x rfl
    obtain ⟨c, hc⟩ := isConj_iff.mp hconj
    refine isConj_iff.mpr ⟨c, ?_⟩
    rw [← pPart_conj, hc, pPart_mul_eq_of_isPElement hp hcomm hx hyreg]

/-- **Vanishing on the `p`-section, restated.**  For a class function, vanishing on `S(x)` is the
same as vanishing at `x y` for every `p`-regular `y ∈ C_G(x)`. -/
theorem forall_pSection_iff {K : Type*} [Zero K] (hp : p.Prime) {x : G} (hx : IsPElement p x)
    (f : G → K) (hf : ∀ g h : G, IsConj g h → f g = f h) :
    (∀ u ∈ pSection p x, f u = 0)
      ↔ ∀ y : ↥(centralizerOf x), IsPRegular p y → f (x * (y : G)) = 0 := by
  constructor
  · intro h y hy
    refine h _ (mul_mem_pSection hp ?_ hx (isPRegular_coe hy))
    exact ((Subgroup.mem_centralizer_iff.mp y.2) x rfl)
  · intro h u hu
    obtain ⟨y, hymem, hyreg, hconj⟩ := (mem_pSection_iff hp hx).mp hu
    rw [hf u _ hconj]
    exact h ⟨y, hymem⟩ (isPRegular_coe_iff.mp hyreg)

end PSection

end OddOrder.RepresentationTheory.Modular
