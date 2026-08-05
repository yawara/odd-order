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
* `OddOrder.RepresentationTheory.Modular.mem_centralizerOf_and_conj_of_conj_mul` — a *specific*
  conjugator taking `x y₁` to `x y₂` already lies in `C_G(x)` and takes `y₁` to `y₂`
* `OddOrder.RepresentationTheory.Modular.isConj_centralizer_of_isConj_mul` — the parametrisation
  is injective: `x y₁ ~_G x y₂` forces `y₁ ~_{C_G(x)} y₂`
* `OddOrder.RepresentationTheory.Modular.centralizerOf_mul_eq_inf` — `C_G(xy) = C_G(x) ⊓ C_G(y)`
* `OddOrder.RepresentationTheory.Modular.mem_pSection_pPart`,
  `OddOrder.RepresentationTheory.Modular.isConj_of_mem_pSection_of_mem_pSection`,
  `OddOrder.RepresentationTheory.Modular.pSection_eq_of_isConj` — the `p`-sections partition `G`,
  indexed by the `G`-classes of `p`-elements
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

/-- **Conjugate elements have conjugate `p`-parts.** -/
theorem isConj_pPart {a b : G} (h : IsConj a b) : IsConj (pPart p a) (pPart p b) := by
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  exact isConj_iff.mpr ⟨c, by rw [← pPart_conj, hc]⟩

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

omit [Finite G] in
/-- **`C_G(x y) = C_G(x) ⊓ C_G(y)`** for a commuting `p`-element `x` and `p`-regular `y`.

Both parts of `x y` are *powers* of `x y` (that is how `pPart` and `pRegularPart` are defined), so
anything centralising `x y` centralises them; the converse is immediate.  This is the identity
that matches the two class-size weights when a sum over the `p`-section `S(x)` is rewritten as a
sum over the `p`-regular classes of `C_G(x)`. -/
theorem centralizerOf_mul_eq_inf (hp : p.Prime) {x y : G} (hcomm : Commute x y)
    (hx : IsPElement p x) (hy : IsPRegular p y) :
    centralizerOf (x * y) = centralizerOf x ⊓ centralizerOf y := by
  refine le_antisymm (fun z hz => ?_) (fun z hz => ?_)
  · have hzc : Commute z (x * y) :=
      (Subgroup.mem_centralizer_iff.mp hz (x * y) rfl).symm
    have hzx : Commute z x := by
      have := commute_pPart_of_commute (p := p) hzc
      rwa [pPart_mul_eq_of_isPElement hp hcomm hx hy] at this
    have hzy : Commute z y := by
      have := commute_pRegularPart_of_commute (p := p) hzc
      rwa [pRegularPart_mul_eq_of_isPElement hp hcomm hx hy] at this
    exact Subgroup.mem_inf.mpr
      ⟨Subgroup.mem_centralizer_iff.mpr fun _ h => h ▸ hzx.symm,
        Subgroup.mem_centralizer_iff.mpr fun _ h => h ▸ hzy.symm⟩
  · obtain ⟨hzx, hzy⟩ := Subgroup.mem_inf.mp hz
    refine Subgroup.mem_centralizer_iff.mpr fun w hw => ?_
    rw [show w = x * y from hw]
    have h1 : Commute z x := (Subgroup.mem_centralizer_iff.mp hzx x rfl).symm
    have h2 : Commute z y := (Subgroup.mem_centralizer_iff.mp hzy y rfl).symm
    exact ((h1.mul_right h2).symm).symm.symm

omit [Finite G] in
/-- **Every element lies in the section of its own `p`-part.**  Together with
`isConj_of_mem_pSection_of_mem_pSection` this says the `p`-sections partition `G`. -/
theorem mem_pSection_pPart (u : G) : u ∈ pSection p (pPart p u) :=
  mem_pSection_iff_isConj_pPart.mpr (IsConj.refl _)

omit [Finite G] in
/-- **Distinct `p`-sections are disjoint.**  If `u` lies in `S(x₁)` and in `S(x₂)` then `x₁` and
`x₂` are both conjugate to the `p`-part of `u`, hence to each other. -/
theorem isConj_of_mem_pSection_of_mem_pSection {x₁ x₂ u : G} (h₁ : u ∈ pSection p x₁)
    (h₂ : u ∈ pSection p x₂) : IsConj x₁ x₂ :=
  (mem_pSection_iff_isConj_pPart.mp h₁).symm.trans (mem_pSection_iff_isConj_pPart.mp h₂)

omit [Finite G] in
/-- **The `p`-section of `x` depends only on the class of `x`.** -/
theorem pSection_eq_of_isConj {x₁ x₂ : G} (h : IsConj x₁ x₂) :
    pSection p x₁ = pSection p x₂ :=
  Set.ext fun _ => ⟨fun hu => mem_pSection_iff_isConj_pPart.mpr
      ((mem_pSection_iff_isConj_pPart.mp hu).trans h),
    fun hu => mem_pSection_iff_isConj_pPart.mpr
      ((mem_pSection_iff_isConj_pPart.mp hu).trans h.symm)⟩

omit [Finite G] in
theorem mem_centralizerOf_and_conj_of_conj_mul (hp : p.Prime) {x y₁ y₂ : G}
    (hx : IsPElement p x) (hy₁ : IsPRegular p y₁) (hy₂ : IsPRegular p y₂)
    (h₁ : y₁ ∈ centralizerOf x) (h₂ : y₂ ∈ centralizerOf x)
    {g : G} (hg : g * (x * y₁) * g⁻¹ = x * y₂) :
    g ∈ centralizerOf x ∧ g * y₁ * g⁻¹ = y₂ := by
  have hcomm₁ : Commute x y₁ := (Subgroup.mem_centralizer_iff.mp h₁) x rfl
  have hcomm₂ : Commute x y₂ := (Subgroup.mem_centralizer_iff.mp h₂) x rfl
  have hpx : g * x * g⁻¹ = x := by
    have h1 : pPart p (g * (x * y₁) * g⁻¹) = pPart p (x * y₂) := by rw [hg]
    rwa [pPart_conj, pPart_mul_eq_of_isPElement hp hcomm₁ hx hy₁,
      pPart_mul_eq_of_isPElement hp hcomm₂ hx hy₂] at h1
  refine ⟨Subgroup.mem_centralizer_iff.mpr ?_, ?_⟩
  · rintro z rfl
    exact (mul_inv_eq_iff_eq_mul.mp hpx).symm
  · have h2 : pRegularPart p (g * (x * y₁) * g⁻¹) = pRegularPart p (x * y₂) := by rw [hg]
    rwa [pRegularPart_conj, pRegularPart_mul_eq_of_isPElement hp hcomm₁ hx hy₁,
      pRegularPart_mul_eq_of_isPElement hp hcomm₂ hx hy₂] at h2

omit [Finite G] in
/-- **The parametrisation of `S(x)` is injective.**  If `x y₁` and `x y₂` are `G`-conjugate, with
`y₁, y₂` `p`-regular in `C_G(x)`, then the conjugating element already lies in `C_G(x)` and
conjugates `y₁` to `y₂`.

Together with `mem_pSection_iff` this says that `{x y_i}` runs over the `G`-classes inside `S(x)`
exactly once as `y_i` runs over the `p`-regular classes of `C_G(x)`. -/
theorem isConj_centralizer_of_isConj_mul (hp : p.Prime) {x y₁ y₂ : G} (hx : IsPElement p x)
    (hy₁ : IsPRegular p y₁) (hy₂ : IsPRegular p y₂)
    (h₁ : y₁ ∈ centralizerOf x) (h₂ : y₂ ∈ centralizerOf x)
    (h : IsConj (x * y₁) (x * y₂)) :
    ∃ g ∈ centralizerOf x, g * y₁ * g⁻¹ = y₂ := by
  obtain ⟨g, hg⟩ := isConj_iff.mp h
  obtain ⟨hmem, hconj⟩ :=
    mem_centralizerOf_and_conj_of_conj_mul hp hx hy₁ hy₂ h₁ h₂ hg
  exact ⟨g, hmem, hconj⟩

end PSection

end OddOrder.RepresentationTheory.Modular
