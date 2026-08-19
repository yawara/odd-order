/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.NearFieldClass
import OddOrder.Isaacs.Ch06_FrobeniusActions.Main
import Mathlib.GroupTheory.SpecificGroups.Quaternion

/-!
# Units of the near-field of order 9 are quaternion

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Part II, Ch. II, step (6) (p. 110): "`F*_{9,2}` is quaternion of
order 8".

* `NearField.eq_neg_one_of_mul_self_eq_one`: in any near-field the only
  involution of the multiplicative group is `-1` — right multiplication by an
  involution `s` is an additive map fixing `a + a·s`, and a fixed-point of a
  nonidentity unit must vanish, so `a·s = -a` for every `a`.
* `unitsMulEquivQuaternionGroup`: the unit group of a noncommutative
  near-field of order `9` is isomorphic to `Q₈`.  It has order `8`, is
  nonabelian, and has a unique involution, so the Isaacs Thm 6.11 engine
  (`isCyclic_or_two_quaternion_of_subgroups_card_prime_unique`) forces the
  generalized quaternion alternative, pinned to `QuaternionGroup 2` by
  cardinality.

This backs the `F ≅ F_{9,2}` branch of step (6): together with
`card_dvd_three_of_odd_mulAutQuaternion` it bounds the odd automorphism
group `Σ` by `|Σ| ∣ 3`.
-/

namespace OddOrder.Peterfalvi.Appendices.NearFields

open Subgroup

/-- **The unique involution of a near-field is `-1`** (Peterfalvi p. 110,
implicit in "`F*_{9,2}` is quaternion").  If `s * s = 1` and `s ≠ 1` then
right multiplication by `s` fixes every `a + a * s`, and a nonzero fixed point
would force `s = 1`; hence `a * s = -a` for all `a`, and `a = 1` gives
`s = -1`. -/
theorem NearField.eq_neg_one_of_mul_self_eq_one {F : Type*} [NearField F]
    {s : F} (hs : s * s = 1) (hne : s ≠ 1) : s = -1 := by
  have key : ∀ a : F, a + a * s = 0 := by
    intro a
    by_contra hb
    have hfix : (a + a * s) * s = a + a * s := by
      rw [NearField.add_mul, mul_assoc, hs, mul_one, add_comm]
    exact hne (mul_left_cancel₀ hb (by rw [hfix, mul_one]))
  have h1 := key 1
  rw [one_mul] at h1
  exact eq_neg_of_add_eq_zero_right h1

/-- Unit form of `NearField.eq_neg_one_of_mul_self_eq_one`: a nonidentity
involution of `Fˣ` has value `-1`. -/
theorem NearField.val_eq_neg_one_of_sq_eq_one {F : Type*} [NearField F]
    {u : Fˣ} (hu : u ^ 2 = 1) (hne : u ≠ 1) : (u : F) = -1 := by
  refine NearField.eq_neg_one_of_mul_self_eq_one ?_ ?_
  · have := congrArg (Units.val) hu
    rwa [Units.val_pow_eq_pow_val, sq, Units.val_one] at this
  · exact fun h => hne (Units.val_eq_one.mp h)

/-- **`F* ≅ Q₈` for a noncommutative near-field of order 9** (Peterfalvi
Part II, Ch. II, step (6), p. 110).  `|Fˣ| = 8`, the group is nonabelian
(commuting units would make `F` commutative), and it has a unique involution
(`-1`), hence a unique subgroup of order `2`; Isaacs Thm 6.11 then leaves the
generalized quaternion alternative, and `|Fˣ| = 8` pins `Q₈`. -/
theorem unitsMulEquivQuaternionGroup {F : Type*} [NearField F]
    (hcard : Nat.card F = 9) (hncomm : ¬ ∀ x y : F, x * y = y * x) :
    Nonempty (Fˣ ≃* QuaternionGroup 2) := by
  classical
  have : Finite F := (Nat.card_pos_iff.mp (by omega)).2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcardU : Nat.card Fˣ = 8 := by
    rw [Nat.card_units, hcard]
  have hP2 : IsPGroup 2 Fˣ := IsPGroup.of_card (n := 3) (by rw [hcardU]; norm_num)
  -- unique subgroup of order 2, via the unique involution `-1`
  have hUnique : ∀ K L : Subgroup Fˣ, Nat.card K = 2 → Nat.card L = 2 → K = L := by
    suffices h : ∀ M N : Subgroup Fˣ, Nat.card M = 2 → Nat.card N = 2 → M ≤ N by
      exact fun K L hK hL => le_antisymm (h K L hK hL) (h L K hL hK)
    intro M N hM hN k hk
    by_cases hk1 : k = 1
    · exact hk1 ▸ one_mem N
    · -- `k` is an involution, hence `↑k = -1`
      have hk2 : k ^ 2 = 1 := by
        have hdvd : orderOf k ∣ 2 := hM ▸ Subgroup.orderOf_dvd_natCard M hk
        rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
        · exact absurd (orderOf_eq_one_iff.mp h1) hk1
        · rw [← h2]; exact pow_orderOf_eq_one k
      have hkval : (k : F) = -1 := NearField.val_eq_neg_one_of_sq_eq_one hk2 hk1
      -- the involution of `N` is also `-1`, so `k ∈ N`
      have : Nontrivial ↥N := Finite.one_lt_card_iff_nontrivial.mp (by omega)
      obtain ⟨y, hy1⟩ := exists_ne (1 : ↥N)
      have hyu : (y : Fˣ) ≠ 1 := fun h => hy1 (OneMemClass.coe_eq_one.mp h)
      have hy2 : (y : Fˣ) ^ 2 = 1 := by
        have hdvd : orderOf (y : Fˣ) ∣ 2 := hN ▸ Subgroup.orderOf_dvd_natCard N y.2
        rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
        · exact absurd (orderOf_eq_one_iff.mp h1) hyu
        · rw [← h2]; exact pow_orderOf_eq_one _
      have hyval : ((y : Fˣ) : F) = -1 :=
        NearField.val_eq_neg_one_of_sq_eq_one hy2 hyu
      have : k = (y : Fˣ) := Units.val_inj.mp (by rw [hkval, hyval])
      exact this ▸ y.2
  rcases OddOrder.Isaacs.Ch06.isCyclic_or_two_quaternion_of_subgroups_card_prime_unique
      hP2 hUnique with hcyc | ⟨-, n, ⟨e⟩⟩
  · -- cyclic units would make `F` commutative
    exfalso
    simp only [not_forall] at hncomm
    obtain ⟨x, y, hxy⟩ := hncomm
    have hx0 : x ≠ 0 := fun h => hxy (by rw [h, zero_mul, mul_zero])
    have hy0 : y ≠ 0 := fun h => hxy (by rw [h, zero_mul, mul_zero])
    have := hcyc
    obtain ⟨g, hgen⟩ := IsCyclic.exists_generator (α := Fˣ)
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hgen (Units.mk0 x hx0))
    obtain ⟨l, hl⟩ := Subgroup.mem_zpowers_iff.mp (hgen (Units.mk0 y hy0))
    have hcomm : Units.mk0 x hx0 * Units.mk0 y hy0
        = Units.mk0 y hy0 * Units.mk0 x hx0 := by
      rw [← hm, ← hl, ← zpow_add, ← zpow_add, add_comm]
    have := congrArg Units.val hcomm
    simpa using absurd this hxy
  · -- pin `n = 2` by cardinality
    have hcards : (8 : ℕ) = Nat.card (QuaternionGroup n) := by
      rw [← hcardU]
      exact Nat.card_congr e.toEquiv
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exfalso
      have : Infinite (ZMod (2 * 0)) := ZMod.infinite
      have : Infinite (QuaternionGroup 0) :=
        Infinite.of_injective (QuaternionGroup.a (n := 0)) fun i j h => by injection h
      rw [Nat.card_eq_zero_of_infinite] at hcards
      omega
    · have : NeZero n := ⟨hn.ne'⟩
      rw [Nat.card_eq_fintype_card, QuaternionGroup.card] at hcards
      have hn2 : n = 2 := by omega
      subst hn2
      exact ⟨e⟩

end OddOrder.Peterfalvi.Appendices.NearFields
