/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Algebra.Polynomial.Roots

/-!
# Lagrange interpolation over a commutative ring with separated nodes

mathlib's `Lagrange` namespace works over a field, where any two distinct nodes have an
invertible difference.  Modular representation theory needs the same construction over the
coefficient ring `𝒪` of a `p`-modular system: there the nodes are the `n`-th roots of unity of
`𝒪`, and their differences are units — not because `𝒪` is a field (it is not), but because
distinct roots of unity have distinct residues (`RootsOfUnityLift`).

This file therefore redevelops the two facts that matter over any commutative ring `R`, given a
finite node set `s` whose pairwise differences are units:

* a polynomial of degree `< #s` vanishing on `s` is zero;
* the Lagrange basis polynomials of `s` sum to `1`.

The second is what turns an annihilating polynomial `∏_{ζ ∈ s} (X - ζ)` into a decomposition of
a module into eigen-submodules, over `𝒪` just as over a field.

## Main results

* `OddOrder.eq_zero_of_degree_lt_card_of_eval_eq_zero`
* `OddOrder.ringLagrangeBasis` and `OddOrder.sum_ringLagrangeBasis`
* `OddOrder.X_sub_C_mul_ringLagrangeBasis` — `(X - ζ) · L_ζ` is a multiple of `∏_{η ∈ s} (X - η)`
-/

namespace OddOrder

open Polynomial

variable {R : Type*} [CommRing R] {s : Finset R} {ζ : R}

/-- The nodes of `s` are pairwise *separated*: distinct members have an invertible difference.
Over a field this holds for every finite set; over a local ring it holds for sets whose members
have distinct residues. -/
def SeparatedNodes (s : Finset R) : Prop :=
  ∀ ζ ∈ s, ∀ η ∈ s, ζ ≠ η → IsUnit (ζ - η)

theorem SeparatedNodes.subset {s t : Finset R} (h : SeparatedNodes t) (hst : s ⊆ t) :
    SeparatedNodes s := fun ζ hζ η hη hne => h ζ (hst hζ) η (hst hη) hne

/-- **A polynomial of degree less than the number of separated nodes that vanishes at all of
them is zero.**  This is the uniqueness half of interpolation, and the only place the
separatedness of the nodes is used. -/
theorem eq_zero_of_degree_lt_card_of_eval_eq_zero :
    ∀ (m : ℕ) {s : Finset R}, s.card = m → SeparatedNodes s →
      ∀ {P : R[X]}, P.degree < (m : ℕ) → (∀ η ∈ s, P.eval η = 0) → P = 0 := by
  classical
  intro m
  induction m with
  | zero =>
    intro s _ _ P hdeg _
    exact degree_eq_bot.mp (Nat.WithBot.lt_zero_iff.mp (by simpa using hdeg))
  | succ j ih =>
    intro s hcard hs P hdeg hroot
    rcases subsingleton_or_nontrivial R with _ | _
    · exact Subsingleton.elim _ _
    obtain ⟨η, hη⟩ : s.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨Q, rfl⟩ : (X - C η) ∣ P := dvd_iff_isRoot.mpr (hroot η hη)
    have hQdeg : Q.degree < (j : ℕ) := by
      have hmul : ((X - C η) * Q).degree = Q.degree + 1 := by
        rw [mul_comm, (monic_X_sub_C η).degree_mul, degree_X_sub_C]
      have hcast : ((j + 1 : ℕ) : WithBot ℕ) = (j : ℕ) + 1 := by push_cast; ring
      rw [hmul, hcast] at hdeg
      exact (WithBot.add_lt_add_iff_right (by simp)).mp hdeg
    have hQroot : ∀ η' ∈ s.erase η, Q.eval η' = 0 := by
      intro η' hη'
      have hne : η' ≠ η := Finset.ne_of_mem_erase hη'
      have h0 : (η' - η) * Q.eval η' = 0 := by
        simpa using hroot η' (Finset.mem_of_mem_erase hη')
      exact (IsUnit.mul_right_eq_zero
        (hs η' (Finset.mem_of_mem_erase hη') η hη hne)).mp h0
    rw [ih (by rw [Finset.card_erase_of_mem hη, hcard]; rfl)
      (hs.subset (Finset.erase_subset _ _)) hQdeg hQroot, mul_zero]

/-! ### The Lagrange basis polynomials -/

open scoped Classical in
/-- The Lagrange basis polynomial of the node set `s` at `ζ`, over a commutative ring:
`L_ζ = u_ζ · ∏_{η ∈ s \ {ζ}} (X - η)`, where `u_ζ` inverts `∏_{η ∈ s \ {ζ}} (ζ - η)` (a unit
when the nodes are separated).  `Ring.inverse` makes this total; the normalisation is correct
exactly on separated node sets. -/
noncomputable def ringLagrangeBasis (s : Finset R) (ζ : R) : R[X] :=
  C (Ring.inverse (∏ η ∈ s.erase ζ, (ζ - η))) * ∏ η ∈ s.erase ζ, (X - C η)

open scoped Classical in
theorem isUnit_prod_sub (hs : SeparatedNodes s) (hζ : ζ ∈ s) :
    IsUnit (∏ η ∈ s.erase ζ, (ζ - η)) :=
  Finset.prod_induction _ IsUnit (fun _ _ => IsUnit.mul) isUnit_one fun η hη =>
    hs ζ hζ η (Finset.mem_of_mem_erase hη) (Finset.ne_of_mem_erase hη).symm

open scoped Classical in
theorem eval_ringLagrangeBasis_self (hs : SeparatedNodes s) (hζ : ζ ∈ s) :
    (ringLagrangeBasis s ζ).eval ζ = 1 := by
  rw [ringLagrangeBasis, eval_mul, eval_C, eval_prod]
  simp only [eval_sub, eval_X, eval_C]
  exact Ring.inverse_mul_cancel _ (isUnit_prod_sub hs hζ)

open scoped Classical in
theorem eval_ringLagrangeBasis_of_ne {η : R} (hη : η ∈ s) (hne : η ≠ ζ) :
    (ringLagrangeBasis s ζ).eval η = 0 := by
  rw [ringLagrangeBasis, eval_mul, eval_prod]
  refine mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hne, hη⟩) ?_)
  simp

open scoped Classical in
theorem degree_ringLagrangeBasis_lt (hζ : ζ ∈ s) :
    (ringLagrangeBasis s ζ).degree < (s.card : ℕ) := by
  have h1 : (∏ η ∈ s.erase ζ, (X - C η)).degree ≤ (((s.erase ζ).card : ℕ) : WithBot ℕ) := by
    refine le_trans (degree_prod_le _ _) (le_trans (Finset.sum_le_sum fun η _ =>
      degree_X_sub_C_le η) ?_)
    simp
  have h2 : (ringLagrangeBasis s ζ).degree ≤ (((s.erase ζ).card : ℕ) : WithBot ℕ) := by
    refine le_trans (degree_mul_le _ _) ?_
    simpa using add_le_add (degree_C_le (a := Ring.inverse (∏ η ∈ s.erase ζ, (ζ - η)))) h1
  refine lt_of_le_of_lt h2 ?_
  rw [Finset.card_erase_of_mem hζ]
  exact_mod_cast Nat.sub_lt (Finset.card_pos.mpr ⟨ζ, hζ⟩) Nat.one_pos

open scoped Classical in
/-- **The Lagrange basis polynomials of a separated node set sum to `1`.**  This is what turns
an annihilating polynomial `∏_{ζ ∈ s} (X - ζ)` into a decomposition into eigen-submodules. -/
theorem sum_ringLagrangeBasis (hs : SeparatedNodes s) (hne : s.Nonempty) :
    ∑ ζ ∈ s, ringLagrangeBasis s ζ = 1 := by
  have hcard : 0 < s.card := Finset.card_pos.mpr hne
  refine sub_eq_zero.mp (eq_zero_of_degree_lt_card_of_eval_eq_zero s.card rfl hs ?_ ?_)
  · refine lt_of_le_of_lt (degree_sub_le _ _) (max_lt ?_ ?_)
    · exact lt_of_le_of_lt (degree_sum_le _ _)
        ((Finset.sup_lt_iff (WithBot.bot_lt_coe _)).mpr fun ζ hζ =>
          degree_ringLagrangeBasis_lt hζ)
    · exact lt_of_le_of_lt degree_one_le (by exact_mod_cast hcard)
  · intro η hη
    rw [eval_sub, eval_finsetSum, eval_one,
      Finset.sum_eq_single_of_mem η hη
        (fun ζ _ hne' => eval_ringLagrangeBasis_of_ne hη (Ne.symm hne')),
      eval_ringLagrangeBasis_self hs hη, sub_self]

open scoped Classical in
/-- `(X - ζ) · L_ζ` is a constant multiple of the full node product, so it annihilates anything
the node product annihilates. -/
theorem X_sub_C_mul_ringLagrangeBasis (hζ : ζ ∈ s) :
    (X - C ζ) * ringLagrangeBasis s ζ
      = C (Ring.inverse (∏ η ∈ s.erase ζ, (ζ - η))) * ∏ η ∈ s, (X - C η) := by
  rw [ringLagrangeBasis, ← Finset.mul_prod_erase s (fun η => X - C η) hζ]
  ring

end OddOrder
