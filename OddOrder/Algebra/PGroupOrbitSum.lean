/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.PGroup

/-!
# Orbit counting for `p`-groups in characteristic `p`

If a `p`-group `P` acts on a finite type `α` and `F : α → A` is constant on `P`-orbits, then in a
setting where `p` annihilates `A` the sum `∑ x, F x` only sees the *fixed points*: every other
orbit has size divisible by `p`, so its contribution vanishes.

This is the additive refinement of `IsPGroup.card_modEq_card_fixedPoints` (which is the case
`F = 1`), and it is the engine behind the multiplicativity of the Brauer homomorphism
`Br_P : (kG)^P → k C_G(P)`.

## Main results

* `OddOrder.sum_eq_sum_fixedPoints`
-/

namespace OddOrder

open MulAction

variable {p : ℕ} {P : Type*} [Group P] {α : Type*} [Fintype α] [MulAction P α]
variable {A : Type*} [AddCommMonoid A]

/-- **Orbit counting in characteristic `p`.**  Let a `p`-group `P` act on a finite type `α`, let
`F : α → A` be constant on `P`-orbits, and suppose `p` annihilates `A`.  Then the sum of `F` over
`α` equals the sum over any finset `s` that describes the fixed points.

The fixed-point set is passed as an explicit finset rather than `MulAction.fixedPoints` so that
the statement carries no decidability instance; in the application `s` is the centraliser
`C_G(P)`. -/
theorem sum_eq_sum_fixedPoints (hp : p.Prime) (hP : IsPGroup p P) (hchar : ∀ a : A, p • a = 0)
    (F : α → A) (hF : ∀ (u : P) (x : α), F (u • x) = F x)
    (s : Finset α) (hs : ∀ x, x ∈ s ↔ ∀ u : P, u • x = x) :
    ∑ x : α, F x = ∑ x ∈ s, F x := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  rw [← Finset.sum_add_sum_compl s F]
  suffices h : ∑ x ∈ sᶜ, F x = 0 by rw [h, add_zero]
  rw [← Finset.sum_fiberwise sᶜ (Quotient.mk'' : α → Quotient (orbitRel P α)) F]
  refine Finset.sum_eq_zero fun b _ => ?_
  rcases (sᶜ.filter fun x => (Quotient.mk'' x : Quotient (orbitRel P α)) = b).eq_empty_or_nonempty
    with hemp | ⟨a, ha⟩
  · rw [hemp, Finset.sum_empty]
  obtain ⟨hacompl, hab⟩ := Finset.mem_filter.mp ha
  have hanotin : a ∉ s := Finset.mem_compl.mp hacompl
  have hmem : ∀ x : α, (Quotient.mk'' x : Quotient (orbitRel P α)) = b ↔ x ∈ orbit P a := by
    intro x
    rw [← hab, Quotient.eq'']
    exact orbitRel_apply
  -- `F` is constant on the fibre.
  have hconst : ∀ x ∈ sᶜ.filter fun x => (Quotient.mk'' x : Quotient (orbitRel P α)) = b,
      F x = F a := by
    intro x hx
    obtain ⟨u, hu⟩ := (hmem x).mp (Finset.mem_filter.mp hx).2
    rw [← hu, hF]
  -- The fibre is the whole orbit: the complement of the fixed points is orbit-stable.
  have hfib : (sᶜ.filter fun x => (Quotient.mk'' x : Quotient (orbitRel P α)) = b)
      = Finset.univ.filter fun x => x ∈ orbit P a := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl, hmem x]
    refine ⟨fun h => h.2, fun hx => ⟨fun hxs => ?_, hx⟩⟩
    obtain ⟨u, hu⟩ := hx
    have hxfix : ∀ v : P, v • x = x := (hs x).mp hxs
    have hua : u • a = x := hu
    have hax : a = x :=
      calc a = u⁻¹ • (u • a) := by rw [smul_smul, inv_mul_cancel, one_smul]
        _ = u⁻¹ • x := by rw [hua]
        _ = x := hxfix u⁻¹
    exact hanotin (hax ▸ hxs)
  have hcard : (sᶜ.filter fun x => (Quotient.mk'' x : Quotient (orbitRel P α)) = b).card
      = Nat.card (orbit P a) := by
    rw [hfib, ← Fintype.card_subtype, Nat.card_eq_fintype_card]
  -- The orbit is nontrivial, hence of size divisible by `p`.
  obtain ⟨n, hn⟩ := hP.card_orbit (α := α) a
  have hne : Nat.card (orbit P a) ≠ 1 := by
    intro h1
    refine hanotin ((hs a).mpr fun v => ?_)
    have : Fintype (orbit P a) := Fintype.ofFinite _
    rw [Nat.card_eq_fintype_card] at h1
    exact mem_fixedPoints.mp (mem_fixedPoints_iff_card_orbit_eq_one.mpr h1) v
  have hn0 : n ≠ 0 := by rintro rfl; exact hne (by simpa using hn)
  obtain ⟨m, hm⟩ : p ∣ Nat.card (orbit P a) := by
    rw [hn]
    exact dvd_pow_self p hn0
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, hcard, hm, mul_comm, mul_nsmul, hchar]

end OddOrder
