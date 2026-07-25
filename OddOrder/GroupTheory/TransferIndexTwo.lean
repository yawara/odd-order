/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.Transfer
import Mathlib.GroupTheory.Abelianization.Defs

/-!
# Transfer for a normal subgroup of index two

Peterfalvi Part II, Ch. II, (17) needs the Hall–Wielandt theorem only in the special
situation `N = N_G(R₂) = R₂⟨s⟩`, where the Sylow subgroup `R₂` is *normal of index `2`*
in `N`.  There the transfer can be computed by hand, and the classical focal-subgroup
machinery is not needed.

This file collects the elementary group theory of that situation.  The key consequence
is `le_commutator_of_conj_mul_mem`: if `s` inverts `P` modulo `⁅N, N⁆` — which is what
a trivial transfer says — and `|P|` is odd, then `P ≤ ⁅N, N⁆`, so the abelianisation of
`N` has no odd part.

See issue 9503.
-/

set_option autoImplicit false

open scoped commutatorElement

namespace OddOrder.GroupTheory

variable {G : Type*} [Group G]

/-- An element of odd order lies in every subgroup containing its square. -/
theorem mem_of_sq_mem_of_odd_orderOf {K : Subgroup G} {x : G} (hodd : Odd (orderOf x))
    (h : x ^ 2 ∈ K) : x ∈ K := by
  obtain ⟨k, hk⟩ := hodd
  have hx : x = (x ^ 2) ^ (k + 1) := by
    rw [← pow_mul]
    calc x = x ^ (orderOf x) * x := by rw [pow_orderOf_eq_one, one_mul]
      _ = x ^ (orderOf x + 1) := by rw [pow_succ]
      _ = x ^ (2 * (k + 1)) := by rw [hk]; ring_nf
  rw [hx]
  exact K.pow_mem h _

/-- **Inverting modulo the derived subgroup absorbs an odd subgroup.**

If `x · x^s ∈ ⁅G, G⁆` for every `x` in a subgroup `P` of odd order, then `P ≤ ⁅G, G⁆`:
the commutator `⁅x⁻¹, s⁆ = x⁻¹·x^s` always lies in `⁅G, G⁆`, so `x²` does, and odd
order lets one take square roots.

This is the group-theoretic heart of "a trivial transfer kills the odd part of the
abelianisation" in the index-two situation. -/
theorem le_commutator_of_conj_mul_mem {P : Subgroup G} {s : G}
    (hodd : ∀ x ∈ P, Odd (orderOf x))
    (hs : ∀ x ∈ P, x * (s * x * s⁻¹) ∈ commutator G) : P ≤ commutator G := by
  intro x hx
  have h1 : x⁻¹ * (s * x * s⁻¹) ∈ commutator G := by
    have hc : ⁅x⁻¹, s⁆ = x⁻¹ * (s * x * s⁻¹) := by
      rw [commutatorElement_def]; group
    rw [← hc, commutator_def]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  have h2 : x ^ 2 ∈ commutator G := by
    have heq : x ^ 2 = (x * (s * x * s⁻¹)) * (x⁻¹ * (s * x * s⁻¹))⁻¹ := by
      rw [pow_two]; group
    rw [heq]
    exact Subgroup.mul_mem _ (hs x hx) (Subgroup.inv_mem _ h1)
  exact mem_of_sq_mem_of_odd_orderOf (hodd x hx) h2

/-- If a subgroup of index `2` is contained in the derived subgroup, the abelianisation
has order dividing `2`; in particular no odd prime divides it. -/
theorem not_dvd_card_abelianization_of_le_commutator [Finite G] {P : Subgroup G}
    (hidx : P.index = 2) (hle : P ≤ commutator G) {p : ℕ} (hp : p.Prime) (hodd : Odd p) :
    ¬ p ∣ Nat.card (Abelianization G) := by
  intro hdvd
  -- `|Ab G| = (commutator G).index` divides `P.index = 2`
  have hcard : Nat.card (Abelianization G) = (commutator G).index :=
    (Subgroup.index_eq_card _).symm
  have hdvd2 : (commutator G).index ∣ 2 := by
    rw [← hidx]
    exact Subgroup.index_dvd_of_le hle
  rw [hcard] at hdvd
  have hple : p ∣ 2 := dvd_trans hdvd hdvd2
  have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hple
  rw [hp2] at hodd
  exact (Nat.not_odd_iff_even.mpr even_two) hodd

end OddOrder.GroupTheory
