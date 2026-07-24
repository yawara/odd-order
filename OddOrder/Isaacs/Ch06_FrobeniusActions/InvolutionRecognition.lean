/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch06_FrobeniusActions.FrobeniusGroup

/-!
# Isaacs FGT Ch.6 — involution recognition helpers for Lemma 6.13 (pp. 192-193)

Involution counting and cyclicity criteria in finite `2`-groups: a nontrivial
`2`-subgroup contains an involution; a commutative `2`-group with a unique involution
(or whose involutions invert a generator) is cyclic; the contradiction lemmas for the
dihedral/semidihedral alternatives of Isaacs Thm 6.12/6.11.

Split from `OddOrder.Isaacs.Ch06_FrobeniusActions.DQSDRecognition` (issue 0149, the
longFile-1500 campaign); `DQSDRecognition` imports this leaf transitively, so
downstream imports are unchanged.
-/

namespace OddOrder.Isaacs.Ch06


open OddOrder.GroupTheory


/-! ### Dihedral / quaternion recognition helpers -/

/-- A nontrivial subgroup of a finite `2`-group contains an involution.

This is the internal-involution half of the Isaacs 6.12 → 6.11 reduction: once a
dihedral or semidihedral alternative supplies an involution outside the cyclic index-two
subgroup, this lemma supplies the nontrivial involution inside that subgroup. -/
theorem exists_involution_mem_of_nontrivial_two_subgroup
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    {C : Subgroup P} (hC_ne : C ≠ ⊥) :
    ∃ z : P, z ∈ C ∧ z ^ 2 = 1 ∧ z ≠ 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hC_two : IsPGroup 2 C := hP.to_subgroup C
  have hC_card_ne_one : Nat.card C ≠ 1 := by
    intro hC_card
    exact hC_ne (Subgroup.eq_bot_of_card_eq C hC_card)
  have hC_card_gt_one : 1 < Nat.card C := by
    have hC_pos : 0 < Nat.card C := Nat.card_pos
    omega
  haveI : Nontrivial C := Finite.one_lt_card_iff_nontrivial.mp hC_card_gt_one
  obtain ⟨n, hn_pos, hC_card⟩ := hC_two.nontrivial_iff_card.mp inferInstance
  have h_two_dvd_card : 2 ∣ Nat.card C := by
    rw [hC_card]
    cases n with
    | zero => omega
    | succ n => exact ⟨2 ^ n, by rw [pow_succ']⟩
  obtain ⟨z, hz_order⟩ := exists_prime_orderOf_dvd_card' (G := C) 2 h_two_dvd_card
  refine ⟨(z : P), z.2, ?_, ?_⟩
  · have hz_sq : z ^ 2 = 1 := by
      rw [← hz_order, pow_orderOf_eq_one]
    exact congrArg Subtype.val hz_sq
  · intro hz_eq_one
    have hz_eq_one' : z = 1 := Subtype.ext hz_eq_one
    have : orderOf z = 1 := by rw [hz_eq_one', orderOf_one]
    exact Nat.prime_two.ne_one (hz_order.symm.trans this)

/-- A finite commutative `2`-group with a unique nontrivial involution is cyclic.

This is the element-level version needed in Isaacs Thm 6.12: it adapts the textbook
“unique involution” hypothesis to the subgroup-level uniqueness used by the finite abelian
`p`-group structure bridge from Thm 6.11. -/
theorem isCyclic_of_comm_two_group_unique_involution
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hcomm : ∀ x y : P, x * y = y * x)
    (hUnique : ∀ x y : P, x ≠ 1 → x ^ 2 = 1 → y ≠ 1 → y ^ 2 = 1 → x = y) :
    IsCyclic P := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : IsMulCommutative P := ⟨⟨hcomm⟩⟩
  refine hP.isCyclic_of_subgroups_card_prime_unique ?_
  intro K L hK_card hL_card
  have hK_two_dvd : 2 ∣ Nat.card K := by rw [hK_card]
  have hL_two_dvd : 2 ∣ Nat.card L := by rw [hL_card]
  obtain ⟨x, hx_order⟩ := exists_prime_orderOf_dvd_card' (G := K) 2 hK_two_dvd
  obtain ⟨y, hy_order⟩ := exists_prime_orderOf_dvd_card' (G := L) 2 hL_two_dvd
  have hx_sq : (x : P) ^ 2 = 1 := by
    have hx_sq_sub : x ^ 2 = 1 := by
      rw [← hx_order, pow_orderOf_eq_one]
    exact congrArg Subtype.val hx_sq_sub
  have hy_sq : (y : P) ^ 2 = 1 := by
    have hy_sq_sub : y ^ 2 = 1 := by
      rw [← hy_order, pow_orderOf_eq_one]
    exact congrArg Subtype.val hy_sq_sub
  have hx_ne : (x : P) ≠ 1 := by
    intro hx_eq_one
    have hx_eq_one' : x = 1 := Subtype.ext hx_eq_one
    have : orderOf x = 1 := by rw [hx_eq_one', orderOf_one]
    exact Nat.prime_two.ne_one (hx_order.symm.trans this)
  have hy_ne : (y : P) ≠ 1 := by
    intro hy_eq_one
    have hy_eq_one' : y = 1 := Subtype.ext hy_eq_one
    have : orderOf y = 1 := by rw [hy_eq_one', orderOf_one]
    exact Nat.prime_two.ne_one (hy_order.symm.trans this)
  have hxy : (x : P) = (y : P) :=
    hUnique (x : P) (y : P) hx_ne hx_sq hy_ne hy_sq
  have hx_order_P : orderOf (x : P) = 2 := orderOf_eq_prime (p := 2) hx_sq hx_ne
  have hy_order_P : orderOf (y : P) = 2 := orderOf_eq_prime (p := 2) hy_sq hy_ne
  have hK_zpowers : Subgroup.zpowers (x : P) = K := by
    apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr x.2)
    rw [hK_card, Nat.card_zpowers, hx_order_P]
  have hL_zpowers : Subgroup.zpowers (y : P) = L := by
    apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr y.2)
    rw [hL_card, Nat.card_zpowers, hy_order_P]
  rw [← hK_zpowers, ← hL_zpowers, hxy]

/-- If every nontrivial involution in a commutative actor inverts a fixed element whose square
is nontrivial, then that actor has a unique nontrivial involution.

This is the action-theoretic core of the Isaacs 6.12 quotient argument: two distinct
involutions would have a product that fixes the element, while the hypothesis says that the
product must invert it. -/
theorem unique_involution_of_comm_of_involutions_invert_element
    {A N : Type*} [Group A] [Group N] [MulDistribMulAction A N]
    (hcomm : ∀ a b : A, a * b = b * a) {n : N} (hn_sq_ne : n ^ 2 ≠ 1)
    (hinv : ∀ a : A, a ≠ 1 → a ^ 2 = 1 → a • n = n⁻¹) :
    ∀ a b : A, a ≠ 1 → a ^ 2 = 1 → b ≠ 1 → b ^ 2 = 1 → a = b := by
  intro a b ha_ne ha_sq hb_ne hb_sq
  by_contra hab
  have hb_inv : b⁻¹ = b := by
    rw [inv_eq_iff_mul_eq_one, ← sq, hb_sq]
  have hab_prod_ne : a * b ≠ 1 := by
    intro hprod
    apply hab
    calc a = a * 1 := by rw [mul_one]
      _ = a * (b * b⁻¹) := by rw [mul_inv_cancel]
      _ = (a * b) * b⁻¹ := by group
      _ = b := by rw [hprod, one_mul, hb_inv]
  have hab_prod_sq : (a * b) ^ 2 = 1 := by
    calc (a * b) ^ 2 = a * b * (a * b) := by rw [pow_two]
      _ = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [hcomm b a]
      _ = a ^ 2 * b ^ 2 := by
        simp [pow_two, mul_assoc]
      _ = 1 := by rw [ha_sq, hb_sq, one_mul]
  have ha_inv : a • n = n⁻¹ := hinv a ha_ne ha_sq
  have hb_inv_n : b • n = n⁻¹ := hinv b hb_ne hb_sq
  have hab_prod_inv : (a * b) • n = n⁻¹ :=
    hinv (a * b) hab_prod_ne hab_prod_sq
  have hab_prod_fix : (a * b) • n = n := by
    rw [mul_smul, hb_inv_n, smul_inv', ha_inv, inv_inv]
  have hn_eq_inv : n = n⁻¹ := hab_prod_fix.symm.trans hab_prod_inv
  apply hn_sq_ne
  rw [pow_two]
  nth_rewrite 1 [hn_eq_inv]
  exact inv_mul_cancel n

/-- A finite commutative `2`-group acting with all involutions inverting a fixed element of
square not equal to `1` is cyclic.

This packages the two Isaacs 6.12 quotient steps: inversion of `c²` gives uniqueness of the
quotient involution, and a commutative finite `2`-group with a unique involution is cyclic. -/
theorem isCyclic_of_comm_two_group_involutions_invert_element
    {A N : Type*} [Group A] [Finite A] [Group N] [MulDistribMulAction A N]
    (hA : IsPGroup 2 A) (hcomm : ∀ a b : A, a * b = b * a)
    {n : N} (hn_sq_ne : n ^ 2 ≠ 1)
    (hinv : ∀ a : A, a ≠ 1 → a ^ 2 = 1 → a • n = n⁻¹) :
    IsCyclic A :=
  isCyclic_of_comm_two_group_unique_involution hA hcomm
    (unique_involution_of_comm_of_involutions_invert_element hcomm hn_sq_ne hinv)

/-- If a subgroup `C` contains a nontrivial involution `z` and there is another involution `a`
outside `C`, then the ambient group has two distinct subgroups of order `2`.

This is the small bridge used to eliminate the dihedral and semidihedral alternatives when
deducing Isaacs Thm 6.11 from Thm 6.12: those groups have an involution outside their cyclic
index-`2` subgroup, whereas generalized quaternion groups do not. -/
theorem exists_distinct_subgroups_card_two_of_external_involution
    {P : Type*} [Group P] [Finite P] {C : Subgroup P} {a z : P}
    (ha_notmem : a ∉ C) (ha_sq : a ^ 2 = 1)
    (hz_mem : z ∈ C) (hz_sq : z ^ 2 = 1) (hz_ne : z ≠ 1) :
    ∃ K L : Subgroup P, Nat.card K = 2 ∧ Nat.card L = 2 ∧ K ≠ L := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ha_ne : a ≠ 1 := by
    intro ha
    exact ha_notmem (ha ▸ C.one_mem)
  have ha_order : orderOf a = 2 := orderOf_eq_prime (p := 2) ha_sq ha_ne
  have hz_order : orderOf z = 2 := orderOf_eq_prime (p := 2) hz_sq hz_ne
  refine ⟨Subgroup.zpowers a, Subgroup.zpowers z, ?_, ?_, ?_⟩
  · rw [Nat.card_zpowers, ha_order]
  · rw [Nat.card_zpowers, hz_order]
  · intro h_eq
    exact ha_notmem ((Subgroup.zpowers_le.mpr hz_mem) (by
      rw [← h_eq]
      exact Subgroup.mem_zpowers a))

/-- If a group has a unique subgroup of order `2`, then it cannot have a nontrivial involution
inside `C` and another involution outside `C`.

This is the contradiction form of the preceding bridge, used when deriving Isaacs Thm 6.11
from Thm 6.12: the dihedral and semidihedral alternatives supply such an outside involution. -/
theorem false_of_unique_subgroups_card_two_of_external_involution
    {P : Type*} [Group P] [Finite P] {C : Subgroup P} {a z : P}
    (hUnique : ∀ K L : Subgroup P, Nat.card K = 2 → Nat.card L = 2 → K = L)
    (ha_notmem : a ∉ C) (ha_sq : a ^ 2 = 1)
    (hz_mem : z ∈ C) (hz_sq : z ^ 2 = 1) (hz_ne : z ≠ 1) :
    False := by
  obtain ⟨K, L, hK_card, hL_card, hKL_ne⟩ :=
    exists_distinct_subgroups_card_two_of_external_involution
      ha_notmem ha_sq hz_mem hz_sq hz_ne
  exact hKL_ne (hUnique K L hK_card hL_card)

/-- If a finite `2`-group has a unique subgroup of order `2`, then no nontrivial subgroup `C`
can have an involution outside it.

This is the packaged 6.12 → 6.11 exclusion used for the dihedral and semidihedral
alternatives: `C` supplies the internal involution, while the alternative supplies the external
one. -/
theorem false_of_unique_subgroups_card_two_of_external_involution_of_nontrivial_two_subgroup
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    {C : Subgroup P}
    (hUnique : ∀ K L : Subgroup P, Nat.card K = 2 → Nat.card L = 2 → K = L)
    (hC_ne : C ≠ ⊥) {a : P} (ha_notmem : a ∉ C) (ha_sq : a ^ 2 = 1) :
    False := by
  obtain ⟨z, hz_mem, hz_sq, hz_ne⟩ :=
    exists_involution_mem_of_nontrivial_two_subgroup hP hC_ne
  exact false_of_unique_subgroups_card_two_of_external_involution
    hUnique ha_notmem ha_sq hz_mem hz_sq hz_ne

/-- Index-two form of the external-involution obstruction.

If `C` has index `2` in a finite `2`-group of order not equal to `2`, then `C` is nontrivial.
Thus any involution outside `C` contradicts uniqueness of the subgroup of order `2`.
This is the exact shape needed for the dihedral and semidihedral alternatives in the
Isaacs 6.12 → 6.11 reduction. -/
theorem false_of_unique_subgroups_card_two_of_external_involution_of_index_two
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    {C : Subgroup P}
    (hUnique : ∀ K L : Subgroup P, Nat.card K = 2 → Nat.card L = 2 → K = L)
    (hC_index : C.index = 2) (hP_card_ne_two : Nat.card P ≠ 2)
    {a : P} (ha_notmem : a ∉ C) (ha_sq : a ^ 2 = 1) :
    False := by
  have hC_ne : C ≠ ⊥ := by
    intro hC_bot
    apply hP_card_ne_two
    have hcard := C.index_mul_card
    rw [hC_index, hC_bot, Subgroup.card_bot] at hcard
    simpa using hcard.symm
  exact false_of_unique_subgroups_card_two_of_external_involution_of_nontrivial_two_subgroup
    hP hUnique hC_ne ha_notmem ha_sq

/-- A finite `2`-group with a unique subgroup of order `2` cannot be a noncyclic
dihedral group.

The reflection `sr 0` gives an involution outside the rotation subgroup, and the rotation
subgroup is nontrivial in the noncyclic cases. -/
theorem false_of_unique_subgroups_card_two_of_dihedral_of_not_isCyclic
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hUnique : ∀ K L : Subgroup P, Nat.card K = 2 → Nat.card L = 2 → K = L)
    (hP_not_cyclic : ¬ IsCyclic P) {n : ℕ}
    (hD : Nonempty (P ≃* DihedralGroup n)) :
    False := by
  classical
  obtain ⟨e⟩ := hD
  have hn_ne_one : n ≠ 1 := by
    intro hn
    apply hP_not_cyclic
    exact e.isCyclic.mpr (DihedralGroup.isCyclic_iff.mpr hn)
  let C : Subgroup P := Subgroup.zpowers (e.symm (DihedralGroup.r 1))
  have hC_ne : C ≠ ⊥ := by
    intro hC_bot
    have hr_mem : e.symm (DihedralGroup.r 1) ∈ C := Subgroup.mem_zpowers _
    have hr_eq_one : e.symm (DihedralGroup.r 1) = 1 := by
      simpa [C, hC_bot] using hr_mem
    have hr_eq_one' : (DihedralGroup.r 1 : DihedralGroup n) = 1 := by
      simpa using congrArg e hr_eq_one
    have horder : orderOf (DihedralGroup.r 1 : DihedralGroup n) = 1 := by
      rw [hr_eq_one', orderOf_one]
    exact hn_ne_one (by
      rw [← DihedralGroup.orderOf_r_one (n := n), horder])
  have hsr_notmem : (DihedralGroup.sr 0 : DihedralGroup n) ∉
      Subgroup.zpowers (DihedralGroup.r 1) := by
    intro hsr
    rcases Subgroup.mem_zpowers_iff.mp hsr with ⟨m, hm⟩
    rw [DihedralGroup.r_one_zpow] at hm
    injection hm
  have ha_notmem : e.symm (DihedralGroup.sr 0) ∉ C := by
    intro ha
    apply hsr_notmem
    rcases Subgroup.mem_zpowers_iff.mp ha with ⟨m, hm⟩
    refine Subgroup.mem_zpowers_iff.mpr ⟨m, ?_⟩
    simpa [C] using congrArg e hm
  have ha_sq : (e.symm (DihedralGroup.sr 0)) ^ 2 = 1 := by
    rw [← map_pow, pow_two, DihedralGroup.sr_mul_self, map_one]
  exact false_of_unique_subgroups_card_two_of_external_involution_of_nontrivial_two_subgroup
    hP hUnique hC_ne ha_notmem ha_sq

/-- A finite `2`-group with a unique subgroup of order `2` cannot be a noncyclic
semidihedral group.

The canonical element `ca 0` is an involution outside the cyclic subgroup generated by `c 1`;
the degenerate `k = 0` case is cyclic and is excluded by `hP_not_cyclic`. -/
theorem false_of_unique_subgroups_card_two_of_semiDihedral_of_not_isCyclic
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hUnique : ∀ K L : Subgroup P, Nat.card K = 2 → Nat.card L = 2 → K = L)
    (hP_not_cyclic : ¬ IsCyclic P) {k : ℕ}
    (hSD : Nonempty (P ≃* SemiDihedralGroup k)) :
    False := by
  classical
  obtain ⟨e⟩ := hSD
  have hk_ne_zero : k ≠ 0 := by
    intro hk
    apply hP_not_cyclic
    rw [hk] at e
    exact e.isCyclic.mpr SemiDihedralGroup.zero_isCyclic
  let C : Subgroup P := Subgroup.zpowers (e.symm (SemiDihedralGroup.c 1))
  have hC_ne : C ≠ ⊥ := by
    intro hC_bot
    have hc_mem : e.symm (SemiDihedralGroup.c 1) ∈ C := Subgroup.mem_zpowers _
    have hc_eq_one : e.symm (SemiDihedralGroup.c 1) = 1 := by
      simpa [C, hC_bot] using hc_mem
    have hc_eq_one' : (SemiDihedralGroup.c 1 : SemiDihedralGroup k) = 1 := by
      simpa using congrArg e hc_eq_one
    have horder : orderOf (SemiDihedralGroup.c 1 : SemiDihedralGroup k) = 1 := by
      rw [hc_eq_one', orderOf_one]
    have hpow_one : 2 ^ k = 1 := by
      rw [← SemiDihedralGroup.orderOf_c_one (n := k), horder]
    exact hk_ne_zero (by
      cases k with
      | zero => rfl
      | succ k =>
          have : (2 : ℕ) ^ (k + 1) ≠ 1 := by
            have hgt : 1 < (2 : ℕ) ^ (k + 1) :=
              one_lt_pow₀ (by norm_num) (by omega)
            omega
          have hpow_one' : (2 : ℕ) ^ (k + 1) = 1 := by
            change (2 : ℕ) ^ (k + 1) = 1 at hpow_one
            exact hpow_one
          exact False.elim (this hpow_one'))
  have hca_notmem : (SemiDihedralGroup.ca 0 : SemiDihedralGroup k) ∉
      Subgroup.zpowers (SemiDihedralGroup.c 1) :=
    SemiDihedralGroup.ca_zero_not_mem_zpowers_c_one k
  have ha_notmem : e.symm (SemiDihedralGroup.ca 0) ∉ C := by
    intro ha
    apply hca_notmem
    rcases Subgroup.mem_zpowers_iff.mp ha with ⟨m, hm⟩
    refine Subgroup.mem_zpowers_iff.mpr ⟨m, ?_⟩
    simpa [C] using congrArg e hm
  have ha_sq : (e.symm (SemiDihedralGroup.ca 0)) ^ 2 = 1 := by
    rw [← map_pow, SemiDihedralGroup.ca_zero_sq, map_one]
  exact false_of_unique_subgroups_card_two_of_external_involution_of_nontrivial_two_subgroup
    hP hUnique hC_ne ha_notmem ha_sq

end OddOrder.Isaacs.Ch06
