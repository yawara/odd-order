/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.Index

/-!
# Relative indices inside a `p`-group

A proper subgroup of a finite `p`-group has index divisible by `p`: the index divides the order
`p ^ n` and is not `1`.

The fact is used both in Isaacs Ch. 9 (Bartels' proof of Theorem 9.28, where it turns
`N_G(P) ≤ M` into `P ∈ Syl_p(G)`) and in block theory (the kernel of the Brauer homomorphism,
where it makes `Tr^P_Q` vanish on `C_G(P)` for every proper `Q < P`), so it lives here rather
than in either.

## Main results

* `OddOrder.dvd_relIndex_of_lt_of_isPGroup`
-/

namespace OddOrder

variable {G : Type*} [Group G]

/-- **A proper subgroup of a finite `p`-group has index divisible by `p`.** -/
theorem dvd_relIndex_of_lt_of_isPGroup {p : ℕ} [Fact p.Prime] [Finite G] {P R : Subgroup G}
    (hR : IsPGroup p ↥R) (hlt : P < R) : p ∣ P.relIndex R := by
  change p ∣ (P.subgroupOf R).index
  have hne : P.subgroupOf R ≠ ⊤ := fun h => by
    rw [Subgroup.subgroupOf_eq_top] at h
    exact absurd (lt_of_lt_of_le hlt h) (lt_irrefl P)
  have hidx1 : (P.subgroupOf R).index ≠ 1 := fun h => hne (Subgroup.index_eq_one.mp h)
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hR
  have hdvd : (P.subgroupOf R).index ∣ p ^ n := hn ▸ Subgroup.index_dvd_card (P.subgroupOf R)
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Fact.out).mp hdvd
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · rw [pow_zero] at hk; exact absurd hk hidx1
  · rw [hk]; exact dvd_pow_self p hkpos.ne'

end OddOrder
