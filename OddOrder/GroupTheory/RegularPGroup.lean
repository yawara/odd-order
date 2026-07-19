/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.OmegaSubgroup

/-!
# `p`-groups of class less than `p`

A `p`-group whose nilpotence class is smaller than `p` behaves, for the purposes
of `p`-th powers, like an abelian group: its elements of order dividing `p` form
a subgroup.  This is the group-theoretic pay-off of Hall's collection formula
(Bender–Glauberman Theorem E.1, proved in
`OddOrder/GroupTheory/HallPetresco.lean`), and it is BG Proposition E.2.

This file collects the two reductions the proof of E.2 runs on, both of them
generic:

* the class bound passes to subgroups (`lowerCentralSeries_eq_bot_of_subgroup`),
  which is what makes an induction on `|G|` possible;
* to know that `Ω₁(G)` has exponent `p` it suffices to know that the `p`-torsion
  elements are closed under multiplication
  (`Omega.pow_eq_one_of_mul_closed`), because then they already form a subgroup.
-/

namespace OddOrder.GroupTheory

variable {G : Type*} [Group G]

/-! ## The class bound passes to subgroups -/

/-- A bound on the nilpotence class is inherited by every subgroup: if
`γ_{n+1}(G) = 1` then `γ_{n+1}(H) = 1` for every `H ≤ G`.  (Indices are
mathlib's: `lowerCentralSeries n` is the book's `γ_{n+1}`.) -/
theorem lowerCentralSeries_eq_bot_of_subgroup (H : Subgroup G) {n : ℕ}
    (h : (⊤ : Subgroup G).lowerCentralSeries n = ⊥) :
    (⊤ : Subgroup ↥H).lowerCentralSeries n = ⊥ := by
  have hle := Subgroup.lowerCentralSeries_map_subtype_le H n
  rw [h, le_bot_iff, Subgroup.map_eq_bot_iff, H.ker_subtype, le_bot_iff] at hle
  exact hle

/-! ## Reducing `Ω₁` to closure under multiplication -/

namespace Omega

/-- If the elements of order dividing `p` are closed under multiplication then
they already form a subgroup, so `Ω₁` consists of exactly those elements — in
particular `Ω₁` has exponent dividing `p`. -/
theorem pow_eq_one_of_mul_closed {p : ℕ}
    (hclosed : ∀ x y : G, x ^ p = 1 → y ^ p = 1 → (x * y) ^ p = 1)
    {g : G} (hg : g ∈ Omega G p 1) : g ^ p = 1 := by
  let S : Subgroup G :=
    { carrier := {x : G | x ^ p = 1}
      one_mem' := one_pow p
      mul_mem' := fun {x y} hx hy => hclosed x y hx hy
      inv_mem' := fun {x} hx => by
        simp only [Set.mem_setOf_eq] at hx ⊢
        rw [inv_pow, hx, inv_one] }
  have hsub : Omega G p 1 ≤ S := by
    refine Subgroup.closure_le S |>.mpr fun x hx => ?_
    simpa [S, pow_one] using hx
  exact hsub hg

end Omega

end OddOrder.GroupTheory
