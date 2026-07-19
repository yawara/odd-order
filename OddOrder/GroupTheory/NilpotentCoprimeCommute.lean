/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch01_Sylow.Main

/-!
# Coprime-order elements of a finite nilpotent group

A finite nilpotent group is the internal direct product of its Sylow subgroups, so two elements
whose orders are coprime lie in complementary sets of factors and therefore commute.

This is a general theorem of finite group theory, with no dependence on either book.  It was
originally written as a helper for Bender--Glauberman Proposition 10.11(d) and lived in
`OddOrder/BG/Ch3_MaximalSubgroups/S10_LocalLemmasCore.lean`; it is used across BG §10-§15 and by
`OddOrder.GroupTheory.CNGroupStructure` (Gorenstein Theorem 12.1.5), which cannot import `BG`.

## Main results

* `commute_of_coprime_orderOf_of_isNilpotent` — coprime-order elements of a finite nilpotent
  group commute.
-/

namespace OddOrder.GroupTheory

open OddOrder.Isaacs

/-- In a finite nilpotent group, two elements of coprime order commute.

A finite nilpotent group is the internal direct product of its Sylow subgroups
(`Sylow.directProductOfNormal`); two coprime-order elements have disjoint sets of relevant
primes, so in every Sylow factor at least one of their components is trivial. -/
theorem commute_of_coprime_orderOf_of_isNilpotent {L : Type*} [Group L] [Finite L]
    [Group.IsNilpotent L] {x y : L} (hxy : Nat.Coprime (orderOf x) (orderOf y)) :
    Commute x y := by
  classical
  haveI := Fintype.ofFinite L
  have hn : ∀ {q : ℕ} [Fact q.Prime] (Q : Sylow q L), Q.Normal := fun Q =>
    Ch01.Sylow.normal_of_isNilpotent Q
  set e := Sylow.directProductOfNormal hn with he
  -- Componentwise: the `(p, P)`-components of `e.symm x` and `e.symm y` commute in the
  -- `p`-group `↥P`, since at least one of them is trivial.
  have hcomp : ∀ (p : (Nat.card L).primeFactors) (P : Sylow (p : ℕ) L),
      Commute (e.symm x p P) (e.symm y p P) := by
    intro p P
    haveI : Fact (p : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors p.2⟩
    -- The order of a component divides the order of the original element.
    have hdvd : ∀ z : L, orderOf (e.symm z p P) ∣ orderOf z := by
      intro z
      apply orderOf_dvd_of_pow_eq_one
      have h1 : (e.symm z) ^ orderOf z = 1 := by rw [← map_pow, pow_orderOf_eq_one, map_one]
      have h2 := congrFun (congrFun h1 p) P
      simpa [Pi.pow_apply, Pi.one_apply] using h2
    -- Each component has prime-power order (it lies in the `p`-group `↥P`).
    have hppow : ∀ z : L, ∃ k, orderOf (e.symm z p P) = (p : ℕ) ^ k := fun z =>
      (IsPGroup.iff_orderOf.mp P.isPGroup') (e.symm z p P)
    by_cases hpx : (p : ℕ) ∣ orderOf x
    · -- Then `p ∤ orderOf y`, so the `y`-component is trivial.
      have hpy : ¬ (p : ℕ) ∣ orderOf y := fun hpy =>
        (Nat.prime_of_mem_primeFactors p.2).ne_one (Nat.dvd_one.mp (hxy ▸ Nat.dvd_gcd hpx hpy))
      obtain ⟨k, hk⟩ := hppow y
      have hk0 : k = 0 := by
        by_contra hkne
        exact hpy ((hk ▸ dvd_pow_self (p : ℕ) hkne).trans (hdvd y))
      have hy1 : e.symm y p P = 1 := orderOf_eq_one_iff.mp (by rw [hk, hk0, pow_zero])
      rw [hy1]; exact Commute.one_right _
    · -- `p ∤ orderOf x`, so the `x`-component is trivial.
      obtain ⟨k, hk⟩ := hppow x
      have hk0 : k = 0 := by
        by_contra hkne
        exact hpx ((hk ▸ dvd_pow_self (p : ℕ) hkne).trans (hdvd x))
      have hx1 : e.symm x p P = 1 := orderOf_eq_one_iff.mp (by rw [hk, hk0, pow_zero])
      rw [hx1]; exact Commute.one_left _
  -- Assemble componentwise commutation, then transport along the isomorphism `e`.
  have hkey : e.symm x * e.symm y = e.symm y * e.symm x := by
    funext p P
    simpa [Pi.mul_apply, commute_iff_eq] using hcomp p P
  have hcong := congrArg e hkey
  rwa [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at hcong

end OddOrder.GroupTheory
