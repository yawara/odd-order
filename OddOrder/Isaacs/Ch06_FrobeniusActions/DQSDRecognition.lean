/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch06_FrobeniusActions.FrobeniusGroup

/-!
# Isaacs FGT Ch.6 (Frobenius actions) — Lemma 6.13/6.14 D/Q/SD recognition + Thm 6.12 first
enlargement (pp. 192-193)
-/

namespace OddOrder.Isaacs.Ch06


open OddOrder.GroupTheory

/-! ### Isaacs Lemma 6.13 + Cor 6.14: D / Q / SD recognition

mmd L3523-3531 (Lem 6.13) + L3533 (Cor 6.14).

Lem 6.13 takes a finite 2-group `P` with a cyclic subgroup `C = ⟨c⟩` of index 2 and an element
`a ∈ P − C`, and classifies `P` according to the action of `a` on `c`:

- If `a * c * a⁻¹ = c⁻¹`, then `P ≃* DihedralGroup (orderOf c)` (when `a² = 1`) or
  `P ≃* QuaternionGroup (orderOf c / 2)` (when `a² ≠ 1`, in which case `a² = z`, the unique
  involution in `C`).
- If `a * c * a⁻¹ = z * c⁻¹` where `z` is the unique involution in `C`, then
  `P ≃* SemiDihedralGroup k` with `2^k = orderOf c`.

Cor 6.14 specializes to `|P| = 8` nonabelian and concludes `P ≃* D_8` or `P ≃* Q_8`
(i.e., `DihedralGroup 4` or `QuaternionGroup 2` in mathlib indexing).

The iso constructions follow mathlib's `quaternionGroupZeroEquivDihedralGroupZero` pattern
(Quaternion.lean L152): element-by-element mapping using the partition `P = C ⊔ aC`, then
`map_mul'` verified by case analysis on the defining relations. -/

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

/-! ### The first enlargement step in Theorem 6.12 -/

/-- **Isaacs Thm 6.12 setup**: if `C` is a normal subgroup of a finite `p`-group `P` and
`C < C_P(C)`, then there is a normal abelian subgroup `B` with `C < B ≤ C_P(C)` and
`|B : C| = p`.

This is the formal version of the first paragraph of the proof of Thm 6.12.  Ch.1 Lemma 1.23
supplies the normal intermediate subgroup of prime relative index; since `B ≤ C_P(C)`,
`C` is central in `B`, and the prime quotient `B/C` is cyclic, so `B` is abelian by
`MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center`. -/
theorem exists_normal_isMulCommutative_relIndex_prime_of_lt_centralizer
    {P : Type*} [Group P] [Finite P] {p : ℕ} [hp : Fact p.Prime]
    (hP : IsPGroup p P)
    {C : Subgroup P} [C.Normal]
    (hC_lt_cent : C < Subgroup.centralizer (C : Set P)) :
    ∃ B : Subgroup P, B.Normal ∧ C < B ∧ B ≤ Subgroup.centralizer (C : Set P) ∧
      C.relIndex B = p ∧ IsMulCommutative B := by
  haveI hCent_normal : (Subgroup.centralizer (C : Set P)).Normal :=
    Subgroup.normal_centralizer
  obtain ⟨B, hB_normal, hC_lt_B, hB_le_cent, hC_rel⟩ :=
    OddOrder.Isaacs.Ch01.IsPGroup.exists_normal_index_eq_prime
      hP (N := C) (M := Subgroup.centralizer (C : Set P)) hC_lt_cent
  haveI hC_sub_normal : (C.subgroupOf B).Normal := inferInstance
  have hC_sub_le_center : C.subgroupOf B ≤ Subgroup.center B := by
    intro c hc
    rw [Subgroup.mem_center_iff]
    intro b
    apply Subtype.ext
    have hb_cent : ((b : B) : P) ∈ Subgroup.centralizer (C : Set P) :=
      hB_le_cent b.2
    have hc_mem : ((c : B) : P) ∈ C := by
      simpa [Subgroup.mem_subgroupOf] using hc
    have h_comm :
        ((c : B) : P) * ((b : B) : P) = ((b : B) : P) * ((c : B) : P) :=
      (Subgroup.mem_centralizer_iff.mp hb_cent) ((c : B) : P) hc_mem
    exact h_comm.symm
  have h_card_quot : Nat.card (B ⧸ C.subgroupOf B) = p := by
    rw [← Subgroup.index_eq_card]
    simpa [Subgroup.relIndex] using hC_rel
  have h_cyclic_quot : IsCyclic (B ⧸ C.subgroupOf B) :=
    isCyclic_of_prime_card h_card_quot
  have hB_comm : ∀ x y : B, x * y = y * x := by
    haveI : IsCyclic (B ⧸ C.subgroupOf B) := h_cyclic_quot
    exact (MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center
      (QuotientGroup.mk' (C.subgroupOf B)) (by
        rw [QuotientGroup.ker_mk']
        exact hC_sub_le_center)).is_comm.comm
  exact ⟨B, hB_normal, hC_lt_B, hB_le_cent, hC_rel, ⟨⟨hB_comm⟩⟩⟩

/-- **Isaacs Thm 6.12 setup**: in a finite group, choose a maximal normal abelian
subgroup.

The conclusion is in the strict-maximality form used by the proof of Theorem 6.12: no
strictly larger normal abelian subgroup contains the chosen subgroup. -/
theorem exists_maximal_normal_isMulCommutative
    {P : Type*} [Group P] [Finite P] :
    ∃ C : Subgroup P, C.Normal ∧ IsMulCommutative C ∧
      ∀ B : Subgroup P, B.Normal → IsMulCommutative B → C < B → False := by
  classical
  let S : Set (Subgroup P) := {C | C.Normal ∧ IsMulCommutative C}
  have hS_nonempty : S.Nonempty := by
    refine ⟨⊥, ?_⟩
    exact ⟨inferInstance, inferInstance⟩
  obtain ⟨C, hC_max⟩ := (Set.toFinite S).exists_maximal hS_nonempty
  refine ⟨C, hC_max.1.1, hC_max.1.2, ?_⟩
  intro B hB_normal hB_comm hC_lt_B
  have hB_mem : B ∈ S := ⟨hB_normal, hB_comm⟩
  exact hC_lt_B.not_ge (hC_max.2 hB_mem hC_lt_B.le)

/-- **Isaacs Thm 6.12 setup**: a maximal normal abelian subgroup `C` of a finite `p`-group
is self-centralizing.

The maximality hypothesis is stated in the form needed for the proof: no strictly larger
normal abelian subgroup contains `C`.  If `C < C_P(C)`, the preceding theorem produces such
a larger normal abelian subgroup, contradiction. -/
theorem centralizer_eq_of_maximal_normal_isMulCommutative
    {P : Type*} [Group P] [Finite P] {p : ℕ} [hp : Fact p.Prime]
    (hP : IsPGroup p P)
    {C : Subgroup P} [C.Normal] (hC_comm : IsMulCommutative C)
    (hC_max : ∀ B : Subgroup P, B.Normal → IsMulCommutative B → C < B → False) :
    Subgroup.centralizer (C : Set P) = C := by
  have hC_le_cent : C ≤ Subgroup.centralizer (C : Set P) := by
    haveI : IsMulCommutative C := hC_comm
    exact Subgroup.le_centralizer (H := C)
  have hcent_le_C : Subgroup.centralizer (C : Set P) ≤ C := by
    by_contra hnot
    have hne : C ≠ Subgroup.centralizer (C : Set P) := by
      intro h_eq
      exact hnot (le_of_eq h_eq.symm)
    have hlt : C < Subgroup.centralizer (C : Set P) := lt_of_le_of_ne hC_le_cent hne
    obtain ⟨B, hB_normal, hC_lt_B, _hB_le_cent, _hC_rel, hB_comm⟩ :=
      exists_normal_isMulCommutative_relIndex_prime_of_lt_centralizer hP hlt
    exact hC_max B hB_normal hB_comm hC_lt_B
  exact le_antisymm hcent_le_C hC_le_cent

private lemma conjNormal_ker_eq_of_self_centralizing
    {P : Type*} [Group P]
    {C : Subgroup P} [C.Normal]
    (hCent : Subgroup.centralizer (C : Set P) = C) :
    (MulAut.conjNormal (H := C) : P →* MulAut C).ker = C := by
  let φ : P →* MulAut C := MulAut.conjNormal (H := C)
  change φ.ker = C
  ext g
  constructor
  · intro hg
    rw [MonoidHom.mem_ker] at hg
    have hg_cent : g ∈ Subgroup.centralizer (C : Set P) := by
      rw [Subgroup.mem_centralizer_iff]
      intro c hc
      let cC : C := ⟨c, hc⟩
      have hfix : φ g cC = cC := by
        have h := congrArg (fun ψ : MulAut C => ψ cC) hg
        simpa using h
      have hconj : g * c * g⁻¹ = c := by
        have hval := congrArg Subtype.val hfix
        simpa [φ, cC] using hval
      have hgc : g * c = c * g := by
        calc g * c = (g * c * g⁻¹) * g := by simp [mul_assoc]
          _ = c * g := by rw [hconj]
      exact hgc.symm
    simpa [hCent] using hg_cent
  · intro hgC
    rw [MonoidHom.mem_ker]
    ext c
    have hg_cent : g ∈ Subgroup.centralizer (C : Set P) := by
      simpa [hCent] using hgC
    have hcomm : (c : P) * g = g * (c : P) :=
      (Subgroup.mem_centralizer_iff.mp hg_cent) (c : P) c.2
    calc ((φ g c : C) : P) = g * (c : P) * g⁻¹ := by rfl
      _ = ((c : P) * g) * g⁻¹ := by rw [← hcomm]
      _ = (c : P) := by simp [mul_assoc]
      _ = (((1 : MulAut C) c : C) : P) := by rfl

/-- **Isaacs Thm 6.12 setup**: if `C` is self-centralizing in `P`, then
`|P/C| ≤ |Aut(C)|`.

The conjugation homomorphism `P → Aut(C)` has kernel `C_P(C)`. Under the
self-centralizing hypothesis this kernel is exactly `C`, so it induces an embedding
`P/C ↪ Aut(C)`. -/
theorem quotient_card_le_mulAut_of_self_centralizing
    {P : Type*} [Group P] [Finite P]
    {C : Subgroup P} [C.Normal]
    (hCent : Subgroup.centralizer (C : Set P) = C) :
    Nat.card (P ⧸ C) ≤ Nat.card (MulAut C) := by
  let φ : P →* MulAut C := MulAut.conjNormal (H := C)
  have hker : φ.ker = C := conjNormal_ker_eq_of_self_centralizing hCent
  let ψ : P ⧸ C →* MulAut C := QuotientGroup.lift C φ (by rw [hker])
  have hψ_inj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    dsimp [ψ]
    rw [QuotientGroup.ker_lift, hker]
    simp
  exact Nat.card_le_card_of_injective ψ hψ_inj

/-- **Isaacs Thm 6.12 setup**: if `C` is cyclic and self-centralizing in `P`, then
`P/C` is abelian.

The conjugation homomorphism `P → Aut(C)` has kernel `C_P(C)`.  Under the self-centralizing
hypothesis this kernel is exactly `C`, so it induces an embedding `P/C ↪ Aut(C)`.  Since the
automorphism group of a cyclic group is abelian, the quotient `P/C` is abelian. -/
theorem quotient_commutative_of_isCyclic_of_self_centralizing
    {P : Type*} [Group P]
    {C : Subgroup P} [C.Normal] (hC_cyclic : IsCyclic C)
    (hCent : Subgroup.centralizer (C : Set P) = C) :
    ∀ x y : P ⧸ C, x * y = y * x := by
  let φ : P →* MulAut C := MulAut.conjNormal (H := C)
  have hker : φ.ker = C := conjNormal_ker_eq_of_self_centralizing hCent
  let ψ : P ⧸ C →* MulAut C := QuotientGroup.lift C φ (by rw [hker])
  have hψ_inj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    dsimp [ψ]
    rw [QuotientGroup.ker_lift, hker]
    simp
  haveI : IsCyclic C := hC_cyclic
  let e := IsCyclic.mulAutMulEquiv C
  letI : CommGroup (MulAut C) := e.toMonoidHom.commGroupOfInjective e.injective
  letI : CommGroup (P ⧸ C) := ψ.commGroupOfInjective hψ_inj
  exact mul_comm

/-- **Isaacs Thm 6.12 setup**: a maximal normal cyclic subgroup `C` makes `P/C`
abelian.

This packages the first paragraph of the proof of Theorem 6.12: maximal normal abelian
subgroups self-centralize in a finite `p`-group, and a cyclic self-centralizing subgroup
forces the quotient to embed in the abelian automorphism group of `C`. -/
theorem quotient_commutative_of_maximal_normal_isCyclic
    {P : Type*} [Group P] [Finite P] {p : ℕ} [hp : Fact p.Prime]
    (hP : IsPGroup p P)
    {C : Subgroup P} [C.Normal] (hC_cyclic : IsCyclic C)
    (hC_max : ∀ B : Subgroup P, B.Normal → IsMulCommutative B → C < B → False) :
    ∀ x y : P ⧸ C, x * y = y * x := by
  have hC_comm : IsMulCommutative C := by
    haveI : IsCyclic C := hC_cyclic
    infer_instance
  have hCent : Subgroup.centralizer (C : Set P) = C :=
    centralizer_eq_of_maximal_normal_isMulCommutative hP hC_comm hC_max
  exact quotient_commutative_of_isCyclic_of_self_centralizing hC_cyclic hCent

/-- **Isaacs Thm 6.12 setup**: from a proper maximal normal cyclic subgroup `C`, choose
the nonabelian normal subgroup `T` with `|T : C| = p`.

This packages the choice of `T/C` of order `p` in the proof of Theorem 6.12.  Ch.1
Lemma 1.23 supplies the normal intermediate subgroup, and maximality of `C` among normal
abelian subgroups makes `T` nonabelian. -/
theorem exists_normal_noncomm_relIndex_prime_of_maximal_normal_zpowers_lt_top
    {P : Type*} [Group P] [Finite P] {p : ℕ} [hp : Fact p.Prime]
    (hP : IsPGroup p P)
    {C : Subgroup P} [C.Normal] {c : P}
    (hC_eq : C = Subgroup.zpowers c)
    (hC_max : ∀ B : Subgroup P, B.Normal → IsMulCommutative B → C < B → False)
    (hC_lt_top : C < ⊤) :
    ∃ T : Subgroup P, T.Normal ∧ c ∈ T ∧ C ≤ T ∧ C.relIndex T = p ∧
      ¬ IsMulCommutative T := by
  obtain ⟨T, hT_normal, hC_lt_T, _hT_le_top, hC_rel⟩ :=
    OddOrder.Isaacs.Ch01.IsPGroup.exists_normal_index_eq_prime
      hP (N := C) (M := ⊤) hC_lt_top
  have hcC : c ∈ C := by
    rw [hC_eq]
    exact Subgroup.mem_zpowers c
  have hT_not_comm : ¬ IsMulCommutative T := by
    intro hT_comm
    exact hC_max T hT_normal hT_comm hC_lt_T
  exact ⟨T, hT_normal, hC_lt_T.le hcC, hC_lt_T.le, hC_rel, hT_not_comm⟩

/-- **Isaacs Thm 6.12 setup**: if `|T : C| = p` and `|C| ≠ 4`, then `|T| ≠ 8`.

This is the small cardinal step in the proof of Theorem 6.12: after excluding the
`|C| = 4` case, the chosen subgroup `T/C` of order `p` cannot have total order `8`. -/
theorem card_ne_eight_of_relIndex_prime_of_card_ne_four
    {P : Type*} [Group P] {p : ℕ} [hp : Fact p.Prime]
    {C T : Subgroup P} (hC_le_T : C ≤ T) (hC_rel : C.relIndex T = p)
    (hC_card_ne : Nat.card C ≠ 4) :
    Nat.card T ≠ 8 := by
  intro hT_card
  let Csub : Subgroup T := C.subgroupOf T
  have hCsub_index : Csub.index = p := hC_rel
  have hquot_card : Nat.card (T ⧸ Csub) = p := by
    rw [← Subgroup.index_eq_card]
    exact hCsub_index
  have hCsub_card : Nat.card Csub = Nat.card C :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hC_le_T).toEquiv
  have hsplit : Nat.card T = Nat.card (T ⧸ Csub) * Nat.card Csub :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup Csub
  have hp_mul : p * Nat.card C = 8 := by
    rw [hquot_card, hCsub_card] at hsplit
    exact hsplit.symm.trans hT_card
  have hp_dvd : p ∣ 8 := ⟨Nat.card C, hp_mul.symm⟩
  have hp_eq_two : p = 2 :=
    Nat.prime_eq_prime_of_dvd_pow (m := 3) (p := p) (q := 2)
      (Fact.out : p.Prime) Nat.prime_two (by simpa using hp_dvd)
  rw [hp_eq_two] at hp_mul
  have hC_card : Nat.card C = 4 := by omega
  exact hC_card_ne hC_card

/-- **Isaacs Thm 6.12 setup**: if `C ≤ T` and `P/C` is abelian, then `T ⊴ P`.

This is the quotient-correspondence step used after choosing `T/C ≤ P/C`: in an abelian
quotient every subgroup is normal, and normality pulls back along the quotient map. -/
theorem normal_of_le_of_quotient_commutative
    {P : Type*} [Group P] {C T : Subgroup P} [C.Normal]
    (hC_le_T : C ≤ T) (hquot_comm : ∀ x y : P ⧸ C, x * y = y * x) :
    T.Normal := by
  let Q : Subgroup (P ⧸ C) := T.map (QuotientGroup.mk' C)
  have hQ_normal : Q.Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hconj : g * n * g⁻¹ = n := by
      rw [hquot_comm g n, mul_assoc, mul_inv_cancel, mul_one]
    rw [hconj]
    exact hn
  have hcomap : Q.comap (QuotientGroup.mk' C) = T := by
    dsimp [Q]
    rw [QuotientGroup.comap_map_mk']
    exact sup_eq_right.mpr hC_le_T
  rw [← hcomap]
  exact hQ_normal.comap (QuotientGroup.mk' C)

/-- **Isaacs Thm 6.12 setup**: after choosing `T/C` of order `p`, a self-centralizing
`C` satisfies `Z(T) < C`.

The inclusion `Z(T) ≤ C` comes from self-centralizing: any central element of `T` centralizes
`C`.  It is strict because otherwise `T/C` is cyclic of prime order and central, forcing `T`
to be abelian. -/
theorem center_lt_subgroupOf_of_self_centralizing_of_relIndex_prime_of_not_isMulCommutative
    {P : Type*} [Group P] [Finite P] {p : ℕ} [hp : Fact p.Prime]
    {C T : Subgroup P} [C.Normal]
    (hC_le_T : C ≤ T) (hCent : Subgroup.centralizer (C : Set P) = C)
    (hC_rel : C.relIndex T = p) (hT_not_comm : ¬ IsMulCommutative T) :
    Subgroup.center T < C.subgroupOf T := by
  have hZ_le_C : Subgroup.center T ≤ C.subgroupOf T := by
    intro z hz
    rw [Subgroup.mem_subgroupOf]
    have hz_cent : ((z : T) : P) ∈ Subgroup.centralizer (C : Set P) := by
      rw [Subgroup.mem_centralizer_iff]
      intro c hc
      have hcomm_T :
          (⟨c, hC_le_T hc⟩ : T) * z = z * ⟨c, hC_le_T hc⟩ :=
        Subgroup.mem_center_iff.mp hz ⟨c, hC_le_T hc⟩
      exact congrArg Subtype.val hcomm_T
    simpa [hCent] using hz_cent
  have hne : Subgroup.center T ≠ C.subgroupOf T := by
    intro hEq
    haveI hCsub_normal : (C.subgroupOf T).Normal := inferInstance
    have h_card_quot : Nat.card (T ⧸ C.subgroupOf T) = p := by
      rw [← Subgroup.index_eq_card]
      simpa [Subgroup.relIndex] using hC_rel
    haveI : IsCyclic (T ⧸ C.subgroupOf T) := isCyclic_of_prime_card h_card_quot
    have hker_le : (QuotientGroup.mk' (C.subgroupOf T)).ker ≤ Subgroup.center T := by
      rw [QuotientGroup.ker_mk']
      exact le_of_eq hEq.symm
    have hT_comm : ∀ x y : T, x * y = y * x :=
      (MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center
        (QuotientGroup.mk' (C.subgroupOf T)) hker_le).is_comm.comm
    exact hT_not_comm ⟨⟨hT_comm⟩⟩
  exact lt_of_le_of_ne hZ_le_C hne

/-- **Isaacs Thm 6.12 setup**: the relative-index computation used before applying
Lemma 6.15.

If `C.subgroupOf T` has index `p` in `T` and `Z(T)` has index `p` in `C.subgroupOf T`,
then `|T : Z(T)| = p²`. -/
theorem center_index_eq_prime_sq_of_subgroupOf_relIndex_prime
    {P : Type*} [Group P] {p : ℕ}
    {C T : Subgroup P}
    (hC_rel : C.relIndex T = p)
    (hZ_le_C : Subgroup.center T ≤ C.subgroupOf T)
    (hZ_rel : (Subgroup.center T).relIndex (C.subgroupOf T) = p) :
    (Subgroup.center T).index = p ^ 2 := by
  have hCsub_index : (C.subgroupOf T).index = p := by
    simpa [Subgroup.relIndex] using hC_rel
  have hmul :
      (Subgroup.center T).relIndex (C.subgroupOf T) * (C.subgroupOf T).index =
        (Subgroup.center T).index :=
    Subgroup.relIndex_mul_index hZ_le_C
  rw [hZ_rel, hCsub_index] at hmul
  simpa [pow_two] using hmul.symm

/-- **Isaacs Thm 6.12 setup**: if `C = ⟨c⟩` and `c^p ∈ Z(T)`, then
`|C : Z(T)| = p`.

The quotient `C / (Z(T) ∩ C)` is cyclic.  The image of `c` has `p`-th power `1`, so
the quotient cardinal divides `p`; because it is also a nontrivial quotient of a `p`-group,
`p` divides its cardinal. -/
theorem center_relIndex_zpowers_eq_prime_of_pow_mem_center
    {T : Type*} [Group T] [Finite T] {p : ℕ} [hp : Fact p.Prime]
    (hT : IsPGroup p T) {c : T}
    (hZ_lt_C : Subgroup.center T < Subgroup.zpowers c)
    (hcp : c ^ p ∈ Subgroup.center T) :
    (Subgroup.center T).relIndex (Subgroup.zpowers c) = p := by
  let C : Subgroup T := Subgroup.zpowers c
  let ZC : Subgroup C := (Subgroup.center T).subgroupOf C
  change (Subgroup.center T).relIndex C = p
  have hZC_le_center : ZC ≤ Subgroup.center C := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro x
    apply Subtype.ext
    have hz_center : ((z : C) : T) ∈ Subgroup.center T := by
      simpa [ZC, Subgroup.mem_subgroupOf] using hz
    exact Subgroup.mem_center_iff.mp hz_center ((x : C) : T)
  haveI hZC_normal : ZC.Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hn_center : n ∈ Subgroup.center C := hZC_le_center hn
    have hgn : g * n = n * g := Subgroup.mem_center_iff.mp hn_center g
    have hconj : g * n * g⁻¹ = n := by
      calc
        g * n * g⁻¹ = n * g * g⁻¹ := by rw [hgn]
        _ = n := by simp
    rwa [hconj]
  let Q := C ⧸ ZC
  haveI hC_cyclic : IsCyclic C := Subgroup.isCyclic_zpowers c
  haveI hQ_cyclic : IsCyclic Q :=
    isCyclic_of_surjective (QuotientGroup.mk' ZC) (QuotientGroup.mk'_surjective ZC)
  have hQ_exp_dvd : Monoid.exponent Q ∣ p := by
    rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective ZC q
    rw [← map_pow]
    refine (QuotientGroup.eq_one_iff (N := ZC) (x ^ p)).mpr ?_
    rw [Subgroup.mem_subgroupOf]
    change ((x : T) ^ p) ∈ Subgroup.center T
    have hx_mem : (x : T) ∈ Subgroup.zpowers c := x.2
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx_mem
    have hxpow : (x : T) ^ p = (c ^ p) ^ k := by
      rw [← hk]
      calc
        (c ^ k) ^ p = (c ^ k) ^ (p : ℤ) := by rw [zpow_natCast]
        _ = c ^ (k * (p : ℤ)) := by rw [← zpow_mul]
        _ = c ^ ((p : ℤ) * k) := by rw [mul_comm]
        _ = (c ^ (p : ℤ)) ^ k := by rw [zpow_mul]
        _ = (c ^ p) ^ k := by rw [zpow_natCast]
    simpa [hxpow] using zpow_mem hcp k
  have hQ_card_dvd_p : Nat.card Q ∣ p := by
    have hcard_exp : Nat.card Q = Monoid.exponent Q :=
      (IsCyclic.exponent_eq_card (α := Q)).symm
    rw [hcard_exp]
    exact hQ_exp_dvd
  have hrel_card : (Subgroup.center T).relIndex C = Nat.card Q := by
    change ZC.index = Nat.card (C ⧸ ZC)
    rw [Subgroup.index_eq_card]
  have hrel_ne_one : (Subgroup.center T).relIndex C ≠ 1 := by
    intro hrel
    have hC_le_Z : C ≤ Subgroup.center T := Subgroup.relIndex_eq_one.mp hrel
    exact hZ_lt_C.ne (le_antisymm hZ_lt_C.le hC_le_Z)
  have hp_dvd_Q_card : p ∣ Nat.card Q := by
    have hQ_p : IsPGroup p Q := (hT.to_subgroup C).to_quotient ZC
    rcases hQ_p.card_eq_or_dvd with hQ_card_one | hdiv
    · exfalso
      exact hrel_ne_one (by rw [hrel_card, hQ_card_one])
    · exact hdiv
  rw [hrel_card]
  exact Nat.dvd_antisymm hQ_card_dvd_p hp_dvd_Q_card

/-- **Dihedral recognition helper** (used in Lem 6.13 inverting case): given a finite group `P`
with `c, a ∈ P` such that `⟨c⟩` has index `2`, `a ∉ ⟨c⟩`, `a² = 1`, and `a c a⁻¹ = c⁻¹`, then
`P ≃* DihedralGroup (orderOf c)`. -/
private noncomputable def dihedralIsoOfInverting
    {P : Type*} [Group P] [Finite P]
    (c a : P) (h_idx : (Subgroup.zpowers c).index = 2)
    (h_a_notmem : a ∉ Subgroup.zpowers c)
    (h_a_sq : a ^ 2 = 1) (h_conj : a * c * a⁻¹ = c⁻¹) :
    P ≃* DihedralGroup (orderOf c) := by
  classical
  set N := orderOf c with hN_def
  haveI : Fintype P := Fintype.ofFinite P
  -- N > 0 since `P` is finite.
  have hc_fin : IsOfFinOrder c := isOfFinOrder_of_finite c
  have hN_pos : 0 < N := hc_fin.orderOf_pos
  haveI : NeZero N := ⟨hN_pos.ne'⟩
  -- Conjugation by `a` inverts every power of `c`.
  have h_conj_zpow : ∀ k : ℤ, a * c ^ k * a⁻¹ = c ^ (-k) := fun k => by
    have step1 : a * c ^ k * a⁻¹ = (a * c * a⁻¹) ^ k := by
      have : Function.Bijective ((MulAut.conj a : P ≃* P) : P → P) :=
        (MulAut.conj a : P ≃* P).bijective
      simp
    rw [step1, h_conj, inv_zpow, ← zpow_neg]
  -- Cardinality computation: |P| = 2 * N.
  have hcard_P : Nat.card P = 2 * N := by
    have h := (Subgroup.zpowers c).index_mul_card
    rw [h_idx, Nat.card_zpowers] at h
    omega
  -- Forward map `DihedralGroup N → P`.
  let fwd : DihedralGroup N → P
    | DihedralGroup.r i => c ^ i.val
    | DihedralGroup.sr i => a * c ^ i.val
  -- Helper: `c ^ (i.val + j.val) = c ^ ((i + j).val)` for `i j : ZMod N`.
  have hc_addval : ∀ i j : ZMod N, c ^ ((i + j).val) = c ^ i.val * c ^ j.val := by
    intro i j
    rw [← pow_add]
    -- `c ^ k = c ^ (k % N)` via `pow_eq_pow_iff_modEq` (since `N = orderOf c`).
    rw [pow_eq_pow_iff_modEq, Nat.ModEq, ← hN_def]
    -- `(i + j).val % N = (i.val + j.val) % N` from `ZMod.val_add`.
    rw [ZMod.val_add, Nat.mod_mod]
  have hc_subval : ∀ i j : ZMod N, c ^ ((j - i).val) = c ^ j.val * (c ^ i.val)⁻¹ := by
    intro i j
    have h := hc_addval (j - i) i
    rw [sub_add_cancel] at h
    -- h : c ^ j.val = c ^ (j - i).val * c ^ i.val
    exact eq_mul_inv_iff_mul_eq.mpr h.symm
  -- `a⁻¹ = a` from `a² = 1`.
  have ha_inv : a⁻¹ = a := by
    have h1 : a * a = 1 := by rw [← sq, h_a_sq]
    exact (eq_inv_of_mul_eq_one_right h1).symm
  -- Commutation: `c ^ k * a = a * c ^ (-k)` for `k : ℤ`.
  have h_zpow_a : ∀ k : ℤ, c ^ k * a = a * c ^ (-k) := fun k => by
    have h := h_conj_zpow (-k)
    rw [neg_neg] at h
    -- h : a * c ^ (-k) * a⁻¹ = c ^ k
    -- Goal: c ^ k * a = a * c ^ (-k)
    rw [show (c ^ k : P) = a * c ^ (-k) * a⁻¹ from h.symm,
        mul_assoc (a * c ^ (-k)), inv_mul_cancel, mul_one]
  -- Bridge: `c ^ ((j - i).val) = c ^ j.val * (c ^ i.val)⁻¹` (already proved as `hc_subval`).
  -- For `h_sr_r`: `c ^ i.val * a * c ^ j.val = a * c ^ (j - i).val`. Use the conjugation
  -- relation, then bridge via `pow_eq_pow_iff_modEq` and ZMod-arithmetic.
  have h_sr_r : ∀ i j : ZMod N, c ^ i.val * a * c ^ j.val = a * c ^ (j - i).val := by
    intro i j
    -- LHS = c^i.val * (a * c^j.val) = c^i.val * a * c^j.val (associativity)
    -- Use h_zpow_a (i.val : ℤ): c^(i.val : ℤ) * a = a * c^(-(i.val : ℤ))
    -- Then combine c^(-(i.val : ℤ)) * c^(j.val : ℤ) = c^(j.val - i.val : ℤ).
    -- Finally show c^(j.val - i.val : ℤ) = c^((j - i).val : ℕ) via mod N.
    have step1 : c ^ i.val * a = a * c ^ (-(i.val : ℤ)) := by
      have := h_zpow_a (i.val : ℤ)
      rw [zpow_natCast] at this; exact this
    rw [step1, mul_assoc, ← zpow_natCast c j.val, ← zpow_add]
    -- Goal: a * c ^ (-(i.val : ℤ) + (j.val : ℤ)) = a * c ^ (j - i).val
    congr 1
    rw [show (c ^ (j - i).val : P) = c ^ ((j - i).val : ℤ) from (zpow_natCast c _).symm,
        zpow_eq_zpow_iff_modEq, ← hN_def]
    -- Bridge `(-i.val + j.val : ℤ) ≡ ((j - i).val : ℤ) [ZMOD (N : ℤ)]` via ZMod equality.
    rw [← ZMod.intCast_eq_intCast_iff]
    push_cast
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    ring
  -- Injectivity: `fwd` does not collapse `c^i.val` and `a * c^j.val` (since `a ∉ ⟨c⟩`),
  -- and is injective on each branch by `orderOf c = N`.
  have hfwd_inj : Function.Injective fwd := by
    rintro (i | i) (j | j) h <;> simp only [fwd] at h
    · -- `c^i.val = c^j.val` ⇒ `i = j` via `pow_eq_pow_iff_modEq`
      congr 1
      have hmod : i.val ≡ j.val [MOD N] := (pow_eq_pow_iff_modEq).mp h
      unfold Nat.ModEq at hmod
      rw [Nat.mod_eq_of_lt (ZMod.val_lt i), Nat.mod_eq_of_lt (ZMod.val_lt j)] at hmod
      exact ZMod.val_injective N hmod
    · -- `c^i.val = a * c^j.val` ⇒ `a ∈ ⟨c⟩`, contradiction
      exfalso
      apply h_a_notmem
      have : a = c ^ i.val * (c ^ j.val)⁻¹ := by
        rw [h]; group
      rw [this]
      exact Subgroup.mul_mem _
        (Subgroup.pow_mem _ (Subgroup.mem_zpowers c) _)
        (Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers c) _))
    · -- `a * c^i.val = c^j.val` ⇒ `a ∈ ⟨c⟩`, contradiction
      exfalso
      apply h_a_notmem
      have : a = c ^ j.val * (c ^ i.val)⁻¹ := by
        rw [← h]; group
      rw [this]
      exact Subgroup.mul_mem _
        (Subgroup.pow_mem _ (Subgroup.mem_zpowers c) _)
        (Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers c) _))
    · -- `a * c^i.val = a * c^j.val` ⇒ `i = j`
      congr 1
      have heq : c ^ i.val = c ^ j.val := mul_left_cancel h
      have hmod : i.val ≡ j.val [MOD N] := (pow_eq_pow_iff_modEq).mp heq
      unfold Nat.ModEq at hmod
      rw [Nat.mod_eq_of_lt (ZMod.val_lt i), Nat.mod_eq_of_lt (ZMod.val_lt j)] at hmod
      exact ZMod.val_injective N hmod
  -- Cardinality equality.
  have hcard_eq : Nat.card (DihedralGroup N) = Nat.card P := by
    rw [DihedralGroup.nat_card, hcard_P]
  -- Build the Equiv via bijectivity.
  have hbij : Function.Bijective fwd := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨hfwd_inj, ?_⟩
    rw [DihedralGroup.card]
    rw [← Nat.card_eq_fintype_card, hcard_P]
  -- Build map_mul (4 cases).
  have hfwd_mul : ∀ x y : DihedralGroup N, fwd (x * y) = fwd x * fwd y := by
    rintro (i | i) (j | j) <;> simp only [fwd]
    · -- r i * r j = r (i+j)
      change c ^ (i + j).val = c ^ i.val * c ^ j.val
      exact hc_addval i j
    · -- r i * sr j = sr (j - i)
      change a * c ^ (j - i).val = c ^ i.val * (a * c ^ j.val)
      rw [← mul_assoc]
      exact (h_sr_r i j).symm
    · -- sr i * r j = sr (i + j)
      change a * c ^ (i + j).val = a * c ^ i.val * c ^ j.val
      rw [mul_assoc, ← hc_addval]
    · -- sr i * sr j = r (j - i)
      change c ^ (j - i).val = a * c ^ i.val * (a * c ^ j.val)
      rw [mul_assoc, ← mul_assoc (c ^ i.val), h_sr_r, ← mul_assoc]
      rw [show a * a = 1 from by rw [← sq, h_a_sq], one_mul]
  -- Assemble.
  let setEquiv : DihedralGroup N ≃ P := Equiv.ofBijective fwd hbij
  exact (MulEquiv.mk' setEquiv hfwd_mul).symm

/-- **Quaternion recognition helper** (used in Lem 6.13 inverting case): given a finite group `P`
with `c, a ∈ P` such that `⟨c⟩` has index `2`, `a ∉ ⟨c⟩`, `orderOf c = 2 * M` with `M > 0`,
`a² = c ^ M` (the unique involution in `⟨c⟩`), and `a c a⁻¹ = c⁻¹`, then
`P ≃* QuaternionGroup M`. -/
private noncomputable def quaternionIsoOfInverting
    {P : Type*} [Group P] [Finite P]
    (c a : P) (M : ℕ) (hM_pos : 0 < M) (h_order : orderOf c = 2 * M)
    (h_idx : (Subgroup.zpowers c).index = 2)
    (h_a_notmem : a ∉ Subgroup.zpowers c)
    (h_a_sq : a ^ 2 = c ^ M) (h_conj : a * c * a⁻¹ = c⁻¹) :
    P ≃* QuaternionGroup M := by
  classical
  haveI : Fintype P := Fintype.ofFinite P
  set N := 2 * M with hN_def
  haveI : NeZero M := ⟨hM_pos.ne'⟩
  haveI : NeZero N := ⟨by positivity⟩
  have hN_pos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have h_orderOf : orderOf c = N := h_order
  -- Conjugation by `a` inverts every power of `c`.
  have h_conj_zpow : ∀ k : ℤ, a * c ^ k * a⁻¹ = c ^ (-k) := fun k => by
    have step1 : a * c ^ k * a⁻¹ = (a * c * a⁻¹) ^ k := by
      have : Function.Bijective ((MulAut.conj a : P ≃* P) : P → P) :=
        (MulAut.conj a : P ≃* P).bijective
      simp
    rw [step1, h_conj, inv_zpow, ← zpow_neg]
  -- Cardinality computation: |P| = 2 * N = 4 * M.
  have hcard_P : Nat.card P = 4 * M := by
    have h := (Subgroup.zpowers c).index_mul_card
    rw [h_idx, Nat.card_zpowers, h_orderOf] at h
    omega
  -- Forward map `QuaternionGroup M → P`.
  let fwd : QuaternionGroup M → P
    | QuaternionGroup.a i => c ^ i.val
    | QuaternionGroup.xa i => a * c ^ i.val
  -- Helpers (mirror dihedral case, with `N = 2 * M`).
  have hc_addval : ∀ i j : ZMod N, c ^ ((i + j).val) = c ^ i.val * c ^ j.val := by
    intro i j
    rw [← pow_add, pow_eq_pow_iff_modEq, Nat.ModEq, h_orderOf, ZMod.val_add, Nat.mod_mod]
  have hc_subval : ∀ i j : ZMod N, c ^ ((j - i).val) = c ^ j.val * (c ^ i.val)⁻¹ := by
    intro i j
    have h := hc_addval (j - i) i
    rw [sub_add_cancel] at h
    exact eq_mul_inv_iff_mul_eq.mpr h.symm
  -- Commutation: `c ^ k * a = a * c ^ (-k)` for `k : ℤ` (uses no `a²` assumption).
  have h_zpow_a : ∀ k : ℤ, c ^ k * a = a * c ^ (-k) := fun k => by
    have h := h_conj_zpow (-k)
    rw [neg_neg] at h
    rw [show (c ^ k : P) = a * c ^ (-k) * a⁻¹ from h.symm,
        mul_assoc (a * c ^ (-k)), inv_mul_cancel, mul_one]
  -- Cross-relation: `c^i.val * a * c^j.val = a * c^(j-i).val`.
  have h_sr_r : ∀ i j : ZMod N, c ^ i.val * a * c ^ j.val = a * c ^ (j - i).val := by
    intro i j
    have step1 : c ^ i.val * a = a * c ^ (-(i.val : ℤ)) := by
      have := h_zpow_a (i.val : ℤ); rw [zpow_natCast] at this; exact this
    rw [step1, mul_assoc, ← zpow_natCast c j.val, ← zpow_add]
    congr 1
    rw [show (c ^ (j - i).val : P) = c ^ ((j - i).val : ℤ) from (zpow_natCast c _).symm,
        zpow_eq_zpow_iff_modEq, h_orderOf]
    rw [← ZMod.intCast_eq_intCast_iff]
    push_cast
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    ring
  -- Injectivity.
  have hfwd_inj : Function.Injective fwd := by
    rintro (i | i) (j | j) h <;> simp only [fwd] at h
    · congr 1
      have hmod : i.val ≡ j.val [MOD N] := by
        rw [← h_orderOf]; exact (pow_eq_pow_iff_modEq).mp h
      unfold Nat.ModEq at hmod
      rw [Nat.mod_eq_of_lt (ZMod.val_lt i), Nat.mod_eq_of_lt (ZMod.val_lt j)] at hmod
      exact ZMod.val_injective N hmod
    · exfalso; apply h_a_notmem
      have : a = c ^ i.val * (c ^ j.val)⁻¹ := by rw [h]; group
      rw [this]
      exact Subgroup.mul_mem _
        (Subgroup.pow_mem _ (Subgroup.mem_zpowers c) _)
        (Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers c) _))
    · exfalso; apply h_a_notmem
      have : a = c ^ j.val * (c ^ i.val)⁻¹ := by rw [← h]; group
      rw [this]
      exact Subgroup.mul_mem _
        (Subgroup.pow_mem _ (Subgroup.mem_zpowers c) _)
        (Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers c) _))
    · congr 1
      have heq : c ^ i.val = c ^ j.val := mul_left_cancel h
      have hmod : i.val ≡ j.val [MOD N] := by
        rw [← h_orderOf]; exact (pow_eq_pow_iff_modEq).mp heq
      unfold Nat.ModEq at hmod
      rw [Nat.mod_eq_of_lt (ZMod.val_lt i), Nat.mod_eq_of_lt (ZMod.val_lt j)] at hmod
      exact ZMod.val_injective N hmod
  -- Bijectivity from cardinality + injectivity.
  have hbij : Function.Bijective fwd := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨hfwd_inj, ?_⟩
    rw [QuaternionGroup.card, ← Nat.card_eq_fintype_card, hcard_P]
  -- map_mul (4 cases: a/a, a/xa, xa/a, xa/xa). Note xa/xa uses `a² = c^M`.
  have hfwd_mul : ∀ x y : QuaternionGroup M, fwd (x * y) = fwd x * fwd y := by
    rintro (i | i) (j | j) <;> simp only [fwd]
    · -- a i * a j = a (i+j)
      change c ^ (i + j).val = c ^ i.val * c ^ j.val
      exact hc_addval i j
    · -- a i * xa j = xa (j - i)
      change a * c ^ (j - i).val = c ^ i.val * (a * c ^ j.val)
      rw [← mul_assoc]; exact (h_sr_r i j).symm
    · -- xa i * a j = xa (i + j)
      change a * c ^ (i + j).val = a * c ^ i.val * c ^ j.val
      rw [mul_assoc, ← hc_addval]
    · -- xa i * xa j = a (↑M + j - i). Uses a² = c^M.
      change c ^ ((↑M + j - i : ZMod N)).val = a * c ^ i.val * (a * c ^ j.val)
      -- Compute RHS: a * c^i.val * a * c^j.val = a² * c^(j-i).val = c^M * c^(j-i).val
      --            = c^(M + j - i).val
      rw [mul_assoc, ← mul_assoc (c ^ i.val), h_sr_r, ← mul_assoc, ← sq, h_a_sq]
      -- Goal: c ^ (↑M + j - i).val = c ^ M * c ^ (j - i).val
      have : c ^ M * c ^ (j - i).val = c ^ ((↑M + (j - i) : ZMod N)).val := by
        rw [hc_addval]
        congr 1
        -- Need: c^M = c^((↑M : ZMod N).val). i.e., `(M : ZMod N).val = M` since M < N.
        rw [show ((↑M : ZMod N).val : ℕ) = M from by
          rw [ZMod.val_natCast]
          exact Nat.mod_eq_of_lt (by rw [hN_def]; omega)]
      rw [this]
      congr 1
      ring_nf
  let setEquiv : QuaternionGroup M ≃ P := Equiv.ofBijective fwd hbij
  exact (MulEquiv.mk' setEquiv hfwd_mul).symm

private lemma eq_pow_half_orderOf_of_mem_zpowers_sq_eq_one
    {P : Type*} [Group P] [Finite P] (c y : P)
    (hy_mem : y ∈ Subgroup.zpowers c) (hy_sq : y ^ 2 = 1) (hy_ne : y ≠ 1) :
    y = c ^ (orderOf c / 2) ∧ orderOf c = 2 * (orderOf c / 2) ∧ 0 < orderOf c / 2 := by
  classical
  have hc_fin : IsOfFinOrder c := isOfFinOrder_of_finite c
  have hN_pos : 0 < orderOf c := hc_fin.orderOf_pos
  have hy_range : y ∈ (Finset.range (orderOf c)).image (fun n : ℕ => c ^ n) :=
    (mem_zpowers_iff_mem_range_orderOf (x := c) (y := y)).mp hy_mem
  rcases Finset.mem_image.mp hy_range with ⟨m, hm_range, hm_eq⟩
  have hm_lt : m < orderOf c := Finset.mem_range.mp hm_range
  have hpow2 : c ^ (2 * m) = 1 := by
    have := hy_sq
    rw [← hm_eq, pow_two, ← pow_add] at this
    simpa [two_mul] using this
  have h_dvd : orderOf c ∣ 2 * m := orderOf_dvd_of_pow_eq_one hpow2
  have h_not_dvd : ¬ orderOf c ∣ m := by
    intro hdm
    apply hy_ne
    rw [← hm_eq]
    exact orderOf_dvd_iff_pow_eq_one.mp hdm
  have hm_pos : 0 < m := by
    by_contra hm_nonpos
    have hm0 : m = 0 := Nat.eq_zero_of_not_pos hm_nonpos
    exact h_not_dvd (by rw [hm0]; exact dvd_zero _)
  rcases h_dvd with ⟨q, hq⟩
  have hq_pos : 0 < q := by
    by_contra hq_nonpos
    have hq0 : q = 0 := Nat.eq_zero_of_not_pos hq_nonpos
    nlinarith
  have hq_lt_two : q < 2 := by
    have hlt : orderOf c * q < orderOf c * 2 := by nlinarith
    exact (Nat.mul_lt_mul_left hN_pos).mp hlt
  have hq_eq : q = 1 := by omega
  have htwo_m : 2 * m = orderOf c := by
    rw [hq_eq, mul_one] at hq
    exact hq
  have hm_half : m = orderOf c / 2 := by omega
  refine ⟨?_, ?_, ?_⟩
  · rw [← hm_half]
    exact hm_eq.symm
  · omega
  · omega

theorem dihedralOrQuaternion_of_invertingConjugation
    {P : Type*} [Group P] [Finite P] (_hP : IsPGroup 2 P)
    (c a : P) (h_idx : (Subgroup.zpowers c).index = 2)
    (h_a_notmem : a ∉ Subgroup.zpowers c)
    (h_conj : a * c * a⁻¹ = c⁻¹) :
    Nonempty (P ≃* DihedralGroup (orderOf c)) ∨
      Nonempty (P ≃* QuaternionGroup (orderOf c / 2)) := by
  classical
  by_cases h_a_sq_one : a ^ 2 = 1
  · left
    exact ⟨dihedralIsoOfInverting c a h_idx h_a_notmem h_a_sq_one h_conj⟩
  · right
    have h_a_sq_mem : a ^ 2 ∈ Subgroup.zpowers c :=
      Subgroup.sq_mem_of_index_two h_idx a
    have h_conj_zpow : ∀ k : ℤ, a * c ^ k * a⁻¹ = c ^ (-k) := fun k => by
      have step1 : a * c ^ k * a⁻¹ = (a * c * a⁻¹) ^ k := by
        have : Function.Bijective ((MulAut.conj a : P ≃* P) : P → P) :=
          (MulAut.conj a : P ≃* P).bijective
        simp
      rw [step1, h_conj, inv_zpow, ← zpow_neg]
    have h_a_sq_sq : (a ^ 2) ^ 2 = 1 := by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h_a_sq_mem
      have h_fixed : a * (c ^ k) * a⁻¹ = c ^ k := by
        rw [hk]
        group
      have h_inv : c ^ k = c ^ (-k) := by
        rw [← h_fixed]
        exact h_conj_zpow k
      calc (a ^ 2) ^ 2 = c ^ k * c ^ k := by rw [← hk, pow_two]
        _ = c ^ k * c ^ (-k) := congrArg (fun t => c ^ k * t) h_inv
        _ = 1 := by rw [← zpow_add, add_neg_cancel, zpow_zero]
    obtain ⟨h_a_sq_half, h_order, h_half_pos⟩ :=
      eq_pow_half_orderOf_of_mem_zpowers_sq_eq_one c (a ^ 2)
        h_a_sq_mem h_a_sq_sq h_a_sq_one
    exact ⟨quaternionIsoOfInverting c a (orderOf c / 2)
      h_half_pos h_order h_idx h_a_notmem h_a_sq_half h_conj⟩

/-- **Semidihedral recognition helper** (normalised twist case): given a finite group `P`
with `c, a ∈ P` such that `⟨c⟩` has index `2`, `a ∉ ⟨c⟩`, `a² = 1`,
`orderOf c = 2^k`, and conjugation by `a` sends `c` to the semidihedral twist
`c ^ (SemiDihedralGroup.twist k).val`, then `P ≃* SemiDihedralGroup k`. -/
private noncomputable def semiDihedralIsoOfTwistNormalized
    {P : Type*} [Group P] [Finite P]
    (c a : P) (k : ℕ) (h_order : orderOf c = 2 ^ k)
    (h_idx : (Subgroup.zpowers c).index = 2)
    (h_a_notmem : a ∉ Subgroup.zpowers c)
    (h_a_sq : a ^ 2 = 1)
    (h_conj : a * c * a⁻¹ = c ^ (SemiDihedralGroup.twist k).val) :
    P ≃* SemiDihedralGroup k := by
  classical
  haveI : Fintype P := Fintype.ofFinite P
  have hN_pos : 0 < 2 ^ k := Nat.two_pow_pos k
  haveI : NeZero (2 ^ k) := ⟨hN_pos.ne'⟩
  set r : ZMod (2 ^ k) := SemiDihedralGroup.twist k with hr_def
  have hcard_P : Nat.card P = 2 * 2 ^ k := by
    have h := (Subgroup.zpowers c).index_mul_card
    rw [h_idx, Nat.card_zpowers, h_order] at h
    omega
  let fwd : SemiDihedralGroup k → P
    | SemiDihedralGroup.c i => c ^ i.val
    | SemiDihedralGroup.ca i => a * c ^ i.val
  have hc_addval : ∀ i j : ZMod (2 ^ k), c ^ ((i + j).val) = c ^ i.val * c ^ j.val := by
    intro i j
    rw [← pow_add, pow_eq_pow_iff_modEq, Nat.ModEq, h_order, ZMod.val_add, Nat.mod_mod]
  have h_conj_pow :
      ∀ i : ZMod (2 ^ k), a * c ^ i.val * a⁻¹ = c ^ (r * i).val := by
    intro i
    have h_map : a * c ^ i.val * a⁻¹ = (a * c * a⁻¹) ^ i.val := by
      simp
    rw [h_map, h_conj, ← pow_mul]
    rw [pow_eq_pow_iff_modEq, Nat.ModEq, h_order]
    rw [ZMod.val_mul, Nat.mod_mod]
  have ha_inv : a⁻¹ = a := by
    have h1 : a * a = 1 := by rw [← sq, h_a_sq]
    exact (eq_inv_of_mul_eq_one_right h1).symm
  have h_pow_a : ∀ i : ZMod (2 ^ k), c ^ i.val * a = a * c ^ (r * i).val := by
    intro i
    have h := h_conj_pow i
    rw [ha_inv] at h
    calc c ^ i.val * a
        = (a * a) * c ^ i.val * a := by rw [show a * a = 1 from by rw [← sq, h_a_sq], one_mul]
      _ = a * (a * c ^ i.val * a) := by group
      _ = a * c ^ (r * i).val := by rw [h]
  have hfwd_inj : Function.Injective fwd := by
    rintro (i | i) (j | j) h <;> simp only [fwd] at h
    · congr 1
      have hmod : i.val ≡ j.val [MOD 2 ^ k] := by
        have hmod0 : i.val ≡ j.val [MOD orderOf c] := (pow_eq_pow_iff_modEq).mp h
        rwa [h_order] at hmod0
      unfold Nat.ModEq at hmod
      rw [Nat.mod_eq_of_lt (ZMod.val_lt i), Nat.mod_eq_of_lt (ZMod.val_lt j)] at hmod
      exact ZMod.val_injective (2 ^ k) hmod
    · exfalso; apply h_a_notmem
      have : a = c ^ i.val * (c ^ j.val)⁻¹ := by rw [h]; group
      rw [this]
      exact Subgroup.mul_mem _
        (Subgroup.pow_mem _ (Subgroup.mem_zpowers c) _)
        (Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers c) _))
    · exfalso; apply h_a_notmem
      have : a = c ^ j.val * (c ^ i.val)⁻¹ := by rw [← h]; group
      rw [this]
      exact Subgroup.mul_mem _
        (Subgroup.pow_mem _ (Subgroup.mem_zpowers c) _)
        (Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers c) _))
    · congr 1
      have heq : c ^ i.val = c ^ j.val := mul_left_cancel h
      have hmod : i.val ≡ j.val [MOD 2 ^ k] := by
        have hmod0 : i.val ≡ j.val [MOD orderOf c] := (pow_eq_pow_iff_modEq).mp heq
        rwa [h_order] at hmod0
      unfold Nat.ModEq at hmod
      rw [Nat.mod_eq_of_lt (ZMod.val_lt i), Nat.mod_eq_of_lt (ZMod.val_lt j)] at hmod
      exact ZMod.val_injective (2 ^ k) hmod
  have hbij : Function.Bijective fwd := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨hfwd_inj, ?_⟩
    rw [SemiDihedralGroup.card, ← Nat.card_eq_fintype_card, hcard_P]
    rw [pow_succ, mul_comm]
  have hfwd_mul : ∀ x y : SemiDihedralGroup k, fwd (x * y) = fwd x * fwd y := by
    rintro (i | i) (j | j) <;> simp only [fwd, SemiDihedralGroup.c_mul_c,
      SemiDihedralGroup.c_mul_ca, SemiDihedralGroup.ca_mul_c, SemiDihedralGroup.ca_mul_ca,
      ← hr_def]
    · exact hc_addval i j
    · rw [← mul_assoc, h_pow_a, mul_assoc, ← hc_addval]
    · rw [mul_assoc, ← hc_addval]
    · calc c ^ (r * i + j).val
          = c ^ (r * i).val * c ^ j.val := hc_addval (r * i) j
        _ = (a * a) * c ^ (r * i).val * c ^ j.val := by
          rw [show a * a = 1 from by rw [← sq, h_a_sq], one_mul]
        _ = a * (a * c ^ (r * i).val) * c ^ j.val := by group
        _ = a * (c ^ i.val * a) * c ^ j.val := by rw [h_pow_a]
        _ = a * c ^ i.val * (a * c ^ j.val) := by group
  let setEquiv : SemiDihedralGroup k ≃ P := Equiv.ofBijective fwd hbij
  exact (MulEquiv.mk' setEquiv hfwd_mul).symm

private lemma pow_twist_eq_pow_half_mul_inv
    {P : Type*} [Group P] [Finite P] (c : P) {k : ℕ}
    (hk : 2 ≤ k) (h_order : orderOf c = 2 ^ k) :
    c ^ (SemiDihedralGroup.twist k).val = c ^ (2 ^ (k - 1)) * c⁻¹ := by
  rw [← zpow_natCast]
  have hrhs : c ^ (2 ^ (k - 1)) * c⁻¹ =
      c ^ (((2 : ℕ) ^ (k - 1) : ℤ) - 1) := by
    simpa [div_eq_mul_inv] using (zpow_natCast_sub_one c (2 ^ (k - 1))).symm
  rw [hrhs, zpow_eq_zpow_iff_modEq, h_order]
  rw [← ZMod.intCast_eq_intCast_iff]
  push_cast
  rw [ZMod.natCast_zmod_val]
  rcases k with _ | _ | n
  · omega
  · omega
  · simp [SemiDihedralGroup.twist]

private lemma twist_conj_zmod_pow
    {P : Type*} [Group P] [Finite P]
    (c a z : P) {k : ℕ} (hk : 2 ≤ k) (h_order : orderOf c = 2 ^ k)
    (h_z_pow : z = c ^ (2 ^ (k - 1)))
    (h_conj : a * c * a⁻¹ = z * c⁻¹) :
    ∀ i : ZMod (2 ^ k),
      a * c ^ i.val * a⁻¹ = c ^ (SemiDihedralGroup.twist k * i).val := by
  intro i
  have h_conj_twist : a * c * a⁻¹ = c ^ (SemiDihedralGroup.twist k).val := by
    rw [h_conj, h_z_pow, ← pow_twist_eq_pow_half_mul_inv c hk h_order]
  have h_map : a * c ^ i.val * a⁻¹ = (a * c * a⁻¹) ^ i.val := by
    simp
  rw [h_map, h_conj_twist, ← pow_mul]
  rw [pow_eq_pow_iff_modEq, Nat.ModEq, h_order]
  rw [ZMod.val_mul, Nat.mod_mod]

private lemma two_mul_eq_zero_of_twist_fixed
    {k : ℕ} (hk : 3 ≤ k) {i : ZMod (2 ^ k)}
    (hfix : SemiDihedralGroup.twist k * i = i) :
    (2 : ZMod (2 ^ k)) * i = 0 := by
  rcases k with _ | _ | _ | n
  · omega
  · omega
  · omega
  · change (2 : ZMod (2 ^ (n + 3))) * i = 0
    change ((2 ^ (n + 2) : ZMod (2 ^ (n + 3))) - 1) * i = i at hfix
    have hzero : (((2 ^ (n + 2) : ZMod (2 ^ (n + 3))) - 2) * i = 0) := by
      have hcalc : (((2 ^ (n + 2) : ZMod (2 ^ (n + 3))) - 2) * i) =
          (((2 ^ (n + 2) : ZMod (2 ^ (n + 3))) - 1) * i - i) := by
        ring
      rw [hcalc, hfix]
      ring
    have hfactor :
        ((2 ^ (n + 2) : ZMod (2 ^ (n + 3))) - 2) =
          (2 : ZMod (2 ^ (n + 3))) *
            ((2 ^ (n + 1) - 1 : ℕ) : ZMod (2 ^ (n + 3))) := by
      rw [Nat.cast_sub (by exact Nat.one_le_two_pow)]
      push_cast
      rw [pow_succ']
      ring
    rw [hfactor] at hzero
    have hodd : Odd (2 ^ (n + 1) - 1) := by
      have h_even : Even (2 ^ (n + 1)) :=
        even_iff_two_dvd.mpr (dvd_pow_self 2 (by omega))
      exact Nat.Even.sub_odd Nat.one_le_two_pow h_even odd_one
    have hcop : Nat.Coprime (2 ^ (n + 1) - 1) (2 ^ (n + 3)) := by
      rw [Nat.coprime_pow_right_iff (by omega), Nat.coprime_two_right]
      exact hodd
    let u := ZMod.unitOfCoprime (2 ^ (n + 1) - 1) hcop
    have hu : (u : ZMod (2 ^ (n + 3))) =
        ((2 ^ (n + 1) - 1 : ℕ) : ZMod (2 ^ (n + 3))) :=
      ZMod.coe_unitOfCoprime _ _
    have hzero' : (u : ZMod (2 ^ (n + 3))) * ((2 : ZMod (2 ^ (n + 3))) * i) = 0 := by
      calc (u : ZMod (2 ^ (n + 3))) * ((2 : ZMod (2 ^ (n + 3))) * i)
          = ((2 : ZMod (2 ^ (n + 3))) *
              ((2 ^ (n + 1) - 1 : ℕ) : ZMod (2 ^ (n + 3)))) * i := by
            rw [hu]
            ring
        _ = 0 := hzero
    exact (Units.mul_right_eq_zero u).mp hzero'

private lemma sq_eq_one_of_mem_zpowers_fixed_by_twist
    {P : Type*} [Group P] [Finite P]
    (c a z y : P) {k : ℕ} (hk_three : 3 ≤ k)
    (h_order : orderOf c = 2 ^ k)
    (h_z_pow : z = c ^ (2 ^ (k - 1)))
    (h_conj : a * c * a⁻¹ = z * c⁻¹)
    (hy_mem : y ∈ Subgroup.zpowers c)
    (hy_fixed : a * y * a⁻¹ = y) :
    y ^ 2 = 1 := by
  classical
  have hk_two : 2 ≤ k := by omega
  have hy_range : y ∈ (Finset.range (orderOf c)).image (fun n : ℕ => c ^ n) :=
    (mem_zpowers_iff_mem_range_orderOf (x := c) (y := y)).mp hy_mem
  rcases Finset.mem_image.mp hy_range with ⟨m, hm_range, hm_eq⟩
  have hm_lt : m < 2 ^ k := by
    have := Finset.mem_range.mp hm_range
    rwa [h_order] at this
  let i : ZMod (2 ^ k) := m
  have hi_val : i.val = m := by
    rw [ZMod.val_natCast]
    exact Nat.mod_eq_of_lt hm_lt
  have hfix_pow : c ^ (SemiDihedralGroup.twist k * i).val = c ^ i.val := by
    calc c ^ (SemiDihedralGroup.twist k * i).val
        = a * c ^ i.val * a⁻¹ :=
          (twist_conj_zmod_pow c a z hk_two h_order h_z_pow h_conj i).symm
      _ = a * c ^ m * a⁻¹ := by rw [hi_val]
      _ = a * y * a⁻¹ := by rw [hm_eq]
      _ = y := hy_fixed
      _ = c ^ m := hm_eq.symm
      _ = c ^ i.val := by rw [hi_val]
  have hfix : SemiDihedralGroup.twist k * i = i := by
    have hmod : (SemiDihedralGroup.twist k * i).val ≡ i.val [MOD 2 ^ k] := by
      have hmod0 : (SemiDihedralGroup.twist k * i).val ≡ i.val [MOD orderOf c] :=
        (pow_eq_pow_iff_modEq).mp hfix_pow
      rwa [h_order] at hmod0
    unfold Nat.ModEq at hmod
    rw [Nat.mod_eq_of_lt (ZMod.val_lt _), Nat.mod_eq_of_lt (ZMod.val_lt _)] at hmod
    exact ZMod.val_injective (2 ^ k) hmod
  have htwo : (2 : ZMod (2 ^ k)) * i = 0 :=
    two_mul_eq_zero_of_twist_fixed hk_three hfix
  have hii : i + i = 0 := by
    simpa [two_mul] using htwo
  have hc_addval : c ^ (i + i).val = c ^ i.val * c ^ i.val := by
    rw [← pow_add, pow_eq_pow_iff_modEq, Nat.ModEq, h_order, ZMod.val_add, Nat.mod_mod]
  calc y ^ 2
      = c ^ i.val * c ^ i.val := by rw [← hm_eq, hi_val, pow_two]
    _ = c ^ (i + i).val := hc_addval.symm
    _ = 1 := by rw [hii, ZMod.val_zero, pow_zero]

lemma zpowers_involution_eq_pow_pred_of_order_two_pow
    {P : Type*} [Group P] [Finite P] (c z : P) {k : ℕ}
    (hk_pos : 0 < k) (h_order : orderOf c = 2 ^ k)
    (h_z_mem : z ∈ Subgroup.zpowers c) (h_z_sq : z ^ 2 = 1) (h_z_ne : z ≠ 1) :
    z = c ^ (2 ^ (k - 1)) := by
  obtain ⟨h_z_half, _h_order_even, _h_half_pos⟩ :=
    eq_pow_half_orderOf_of_mem_zpowers_sq_eq_one c z h_z_mem h_z_sq h_z_ne
  have hhalf : 2 ^ k / 2 = 2 ^ (k - 1) := by
    rcases k with _ | k
    · omega
    · simp [pow_succ]
  rw [h_z_half, h_order, hhalf]

/-- In a finite cyclic `2`-group of order larger than `2`, the nontrivial involution is a
square.

This is the cyclic-quotient square-root step in Isaacs Thm 6.12: if the cyclic quotient
`P/C` has order larger than `2`, then its unique involution coset is a square. -/
theorem exists_sq_eq_of_isCyclic_two_group_involution_of_card_ne_two
    {Q : Type*} [Group Q] [Finite Q] (hQ : IsPGroup 2 Q) [IsCyclic Q]
    {x : Q} (hx_ne : x ≠ 1) (hx_sq : x ^ 2 = 1) (hcard_ne_two : Nat.card Q ≠ 2) :
    ∃ y : Q, y ^ 2 = x := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg_gen⟩ := IsCyclic.exists_generator (α := Q)
  obtain ⟨k, hcard⟩ := (IsPGroup.iff_card (p := 2) (G := Q)).mp hQ
  have hcard_ne_one : Nat.card Q ≠ 1 := by
    intro hcard_one
    haveI : Subsingleton Q := (Nat.card_eq_one_iff_unique.mp hcard_one).1
    exact hx_ne (Subsingleton.elim x 1)
  have hk_pos : 0 < k := by
    by_contra hk_not
    have hk_zero : k = 0 := Nat.eq_zero_of_not_pos hk_not
    apply hcard_ne_one
    rw [hcard, hk_zero, pow_zero]
  have hk_ne_one : k ≠ 1 := by
    intro hk_one
    apply hcard_ne_two
    rw [hcard, hk_one, pow_one]
  have hk_two : 2 ≤ k := by omega
  have hg_order : orderOf g = 2 ^ k := by
    rw [← hcard]
    exact orderOf_eq_card_of_forall_mem_zpowers hg_gen
  have hx_mem : x ∈ Subgroup.zpowers g := hg_gen x
  have hx_eq : x = g ^ (2 ^ (k - 1)) :=
    zpowers_involution_eq_pow_pred_of_order_two_pow g x hk_pos hg_order hx_mem hx_sq hx_ne
  refine ⟨g ^ (2 ^ (k - 2)), ?_⟩
  rw [hx_eq, ← pow_mul]
  congr 1
  rw [show k - 1 = k - 2 + 1 by omega, pow_succ]

private lemma square_eq_one_or_unique_involution_of_square_sq_one
    {P : Type*} [Group P] (c a z : P)
    (h_idx : (Subgroup.zpowers c).index = 2)
    (h_z_unique : ∀ y ∈ Subgroup.zpowers c, y ^ 2 = 1 → y ≠ 1 → y = z)
    (h_a_sq_sq : (a ^ 2) ^ 2 = 1) :
    a ^ 2 = 1 ∨ a ^ 2 = z := by
  by_cases h_a_sq_one : a ^ 2 = 1
  · exact Or.inl h_a_sq_one
  · exact Or.inr (h_z_unique (a ^ 2)
      (Subgroup.sq_mem_of_index_two h_idx a) h_a_sq_sq h_a_sq_one)

private lemma two_le_exponent_of_nonabelian_index_two
    {P : Type*} [Group P] [Finite P] (c : P) {k : ℕ}
    (h_nonab : ∃ x y : P, x * y ≠ y * x)
    (h_idx : (Subgroup.zpowers c).index = 2)
    (h_order : orderOf c = 2 ^ k)
    (hk_pos : 0 < k) :
    2 ≤ k := by
  by_contra hk_not
  have hk_eq : k = 1 := by omega
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card P = 2 ^ 2 := by
    have h := (Subgroup.zpowers c).index_mul_card
    rw [h_idx, Nat.card_zpowers, h_order, hk_eq] at h
    omega
  obtain ⟨x, y, hxy⟩ := h_nonab
  exact hxy ((isMulCommutative_iff.mp
    (IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) hcard)) x y)

private lemma commutative_of_index_two_zpowers_of_commute_generator
    {P : Type*} [Group P] (c a : P)
    (h_idx : (Subgroup.zpowers c).index = 2)
    (h_a_notmem : a ∉ Subgroup.zpowers c)
    (h_comm : Commute a c) :
    ∀ x y : P, x * y = y * x := by
  let C := Subgroup.zpowers c
  have h_a_inv_notmem : a⁻¹ ∉ C := by
    intro ha
    exact h_a_notmem (C.inv_mem_iff.mp ha)
  have h_repr : ∀ x : P, (∃ m : ℤ, c ^ m = x) ∨ ∃ m : ℤ, x = a * c ^ m := by
    intro x
    by_cases hx : x ∈ C
    · left
      exact Subgroup.mem_zpowers_iff.mp hx
    · right
      have hax : a⁻¹ * x ∈ C := by
        rw [Subgroup.mul_mem_iff_of_index_two h_idx]
        exact iff_of_false h_a_inv_notmem hx
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hax
      exact ⟨m, by
        calc x = a * (a⁻¹ * x) := by group
          _ = a * c ^ m := by rw [← hm]⟩
  intro x y
  rcases h_repr x with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · rcases h_repr y with ⟨n, rfl⟩ | ⟨n, rfl⟩
    · exact (Commute.zpow_zpow_self c m n).eq
    · have hcm_a : Commute (c ^ m) a := h_comm.symm.zpow_left m
      calc c ^ m * (a * c ^ n)
          = a * (c ^ m * c ^ n) := hcm_a.left_comm (c ^ n)
        _ = a * (c ^ n * c ^ m) := by rw [(Commute.zpow_zpow_self c m n).eq]
        _ = a * c ^ n * c ^ m := by group
  · rcases h_repr y with ⟨n, rfl⟩ | ⟨n, rfl⟩
    · have hcn_a : Commute (c ^ n) a := h_comm.symm.zpow_left n
      calc (a * c ^ m) * c ^ n
          = a * (c ^ m * c ^ n) := by group
        _ = a * (c ^ n * c ^ m) := by rw [(Commute.zpow_zpow_self c m n).eq]
        _ = c ^ n * (a * c ^ m) := by rw [hcn_a.left_comm]
    · have ham : Commute a (c ^ m) := h_comm.zpow_right m
      have han : Commute a (c ^ n) := h_comm.zpow_right n
      calc (a * c ^ m) * (a * c ^ n)
          = a * a * (c ^ m * c ^ n) := by
            rw [mul_assoc, ham.symm.left_comm]
            group
        _ = a * a * (c ^ n * c ^ m) := by rw [(Commute.zpow_zpow_self c m n).eq]
        _ = a * (a * c ^ n) * c ^ m := by group
        _ = a * (c ^ n * a) * c ^ m := by rw [han.eq]
        _ = (a * c ^ n) * (a * c ^ m) := by
            group

private lemma three_le_exponent_of_nonabelian_twist
    {P : Type*} [Group P] [Finite P] (c a z : P) {k : ℕ}
    (h_nonab : ∃ x y : P, x * y ≠ y * x)
    (h_idx : (Subgroup.zpowers c).index = 2)
    (h_a_notmem : a ∉ Subgroup.zpowers c)
    (hk : 2 ≤ k)
    (h_z_pow : z = c ^ (2 ^ (k - 1)))
    (h_conj : a * c * a⁻¹ = z * c⁻¹) :
    3 ≤ k := by
  by_contra hk_not
  have hk_eq : k = 2 := by omega
  have h_conj_c : a * c * a⁻¹ = c := by
    rw [h_conj, h_z_pow, hk_eq]
    norm_num
    group
  have h_comm : Commute a c := by
    change a * c = c * a
    calc a * c = (a * c * a⁻¹) * a := by group
      _ = c * a := by rw [h_conj_c]
  obtain ⟨x, y, hxy⟩ := h_nonab
  exact hxy (commutative_of_index_two_zpowers_of_commute_generator c a
    h_idx h_a_notmem h_comm x y)

private noncomputable def semiDihedralIsoOfTwistInvolution
    {P : Type*} [Group P] [Finite P]
    (c a z : P) (k : ℕ) (hk : 2 ≤ k) (h_order : orderOf c = 2 ^ k)
    (h_idx : (Subgroup.zpowers c).index = 2)
    (h_a_notmem : a ∉ Subgroup.zpowers c)
    (h_z_pow : z = c ^ (2 ^ (k - 1)))
    (h_a_sq : a ^ 2 = 1)
    (h_conj : a * c * a⁻¹ = z * c⁻¹) :
    P ≃* SemiDihedralGroup k := by
  refine semiDihedralIsoOfTwistNormalized c a k h_order h_idx h_a_notmem h_a_sq ?_
  rw [h_conj, h_z_pow, ← pow_twist_eq_pow_half_mul_inv c hk h_order]

private noncomputable def semiDihedralIsoOfTwistSquareInvolution
    {P : Type*} [Group P] [Finite P]
    (c a z : P) (k : ℕ) (hk : 2 ≤ k) (h_order : orderOf c = 2 ^ k)
    (h_idx : (Subgroup.zpowers c).index = 2)
    (h_a_notmem : a ∉ Subgroup.zpowers c)
    (h_z_mem : z ∈ Subgroup.zpowers c)
    (h_z_pow : z = c ^ (2 ^ (k - 1)))
    (h_z_sq : z ^ 2 = 1)
    (h_a_sq : a ^ 2 = z)
    (h_conj : a * c * a⁻¹ = z * c⁻¹) :
    P ≃* SemiDihedralGroup k := by
  classical
  have hz_comm : Commute z c := by
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp h_z_mem
    rw [← hm]
    exact Commute.zpow_self c m
  have h_ca_notmem : c * a ∉ Subgroup.zpowers c := by
    intro hca
    apply h_a_notmem
    have ha : a = c⁻¹ * (c * a) := by group
    rw [ha]
    exact Subgroup.mul_mem _
      (Subgroup.inv_mem _ (Subgroup.mem_zpowers c))
      hca
  have h_ca_sq : (c * a) ^ 2 = 1 := by
    calc (c * a) ^ 2
        = (c * a) * (c * a) := by rw [pow_two]
      _ = c * (a * c * a⁻¹) * a ^ 2 := by group
      _ = c * (z * c⁻¹) * z := by rw [h_conj, h_a_sq]
      _ = (c * z * c⁻¹) * z := by group
      _ = z * z := by rw [hz_comm.symm.mul_inv_cancel]
      _ = 1 := by rw [← pow_two, h_z_sq]
  have h_ca_conj : (c * a) * c * (c * a)⁻¹ = z * c⁻¹ := by
    calc (c * a) * c * (c * a)⁻¹
        = c * (a * c * a⁻¹) * c⁻¹ := by group
      _ = c * (z * c⁻¹) * c⁻¹ := by rw [h_conj]
      _ = (c * z * c⁻¹) * c⁻¹ := by group
      _ = z * c⁻¹ := by rw [hz_comm.symm.mul_inv_cancel]
  exact semiDihedralIsoOfTwistInvolution c (c * a) z k hk h_order h_idx
    h_ca_notmem h_z_pow h_ca_sq h_ca_conj

/-- **Isaacs Lemma 6.13 (twist case)**: Let `P` be a finite nonabelian 2-group with a cyclic
subgroup `C = ⟨c⟩` of index `2`, and `a ∈ P − C` with `a * c * a⁻¹ = z * c⁻¹` where `z` is
the unique involution in `C`. Then `P ≃* SemiDihedralGroup k` where `2 ^ k = orderOf c`. -/
theorem semiDihedral_of_twistConjugation
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (h_nonab : ∃ x y : P, x * y ≠ y * x)
    (c a z : P) (h_idx : (Subgroup.zpowers c).index = 2)
    (h_a_notmem : a ∉ Subgroup.zpowers c)
    (h_z_mem : z ∈ Subgroup.zpowers c) (h_z_sq : z ^ 2 = 1) (h_z_ne : z ≠ 1)
    (h_z_unique : ∀ y ∈ Subgroup.zpowers c, y ^ 2 = 1 → y ≠ 1 → y = z)
    (h_conj : a * c * a⁻¹ = z * c⁻¹) :
    ∃ k : ℕ, 2 ^ k = orderOf c ∧ Nonempty (P ≃* SemiDihedralGroup k) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, h_order⟩ := (IsPGroup.iff_orderOf.mp hP) c
  have hk_pos : 0 < k := by
    obtain ⟨_h_z_half, _h_order_even, h_half_pos⟩ :=
      eq_pow_half_orderOf_of_mem_zpowers_sq_eq_one c z h_z_mem h_z_sq h_z_ne
    by_contra hk_not
    have hk0 : k = 0 := Nat.eq_zero_of_not_pos hk_not
    rw [h_order, hk0] at h_half_pos
    norm_num at h_half_pos
  have hk_two : 2 ≤ k :=
    two_le_exponent_of_nonabelian_index_two c h_nonab h_idx h_order hk_pos
  have h_z_pow : z = c ^ (2 ^ (k - 1)) :=
    zpowers_involution_eq_pow_pred_of_order_two_pow c z hk_pos h_order
      h_z_mem h_z_sq h_z_ne
  have hk_three : 3 ≤ k :=
    three_le_exponent_of_nonabelian_twist c a z h_nonab h_idx h_a_notmem
      hk_two h_z_pow h_conj
  have h_a_sq_sq : (a ^ 2) ^ 2 = 1 := by
    exact sq_eq_one_of_mem_zpowers_fixed_by_twist c a z (a ^ 2)
      hk_three h_order h_z_pow h_conj
      (Subgroup.sq_mem_of_index_two h_idx a)
      (by group)
  refine ⟨k, h_order.symm, ?_⟩
  rcases square_eq_one_or_unique_involution_of_square_sq_one c a z
      h_idx h_z_unique h_a_sq_sq with h_a_sq | h_a_sq
  · exact ⟨semiDihedralIsoOfTwistInvolution c a z k hk_two h_order h_idx
      h_a_notmem h_z_pow h_a_sq h_conj⟩
  · exact ⟨semiDihedralIsoOfTwistSquareInvolution c a z k hk_two h_order h_idx
      h_a_notmem h_z_mem h_z_pow h_z_sq h_a_sq h_conj⟩

private lemma exists_sq_ne_one_of_nonabelian
    {P : Type*} [Group P] (h_nonab : ∃ x y : P, x * y ≠ y * x) :
    ∃ c : P, c ^ 2 ≠ 1 := by
  by_contra h
  push Not at h
  obtain ⟨x, y, hxy⟩ := h_nonab
  have hx_inv : x⁻¹ = x := by
    exact inv_eq_of_mul_eq_one_right (by rw [← pow_two, h x])
  have hy_inv : y⁻¹ = y := by
    exact inv_eq_of_mul_eq_one_right (by rw [← pow_two, h y])
  have hxy_inv : (x * y)⁻¹ = x * y := by
    exact inv_eq_of_mul_eq_one_right (by rw [← pow_two, h (x * y)])
  apply hxy
  calc x * y
      = (x * y)⁻¹ := hxy_inv.symm
    _ = y⁻¹ * x⁻¹ := by rw [mul_inv_rev]
    _ = y * x := by rw [hy_inv, hx_inv]

private lemma exists_orderOf_eq_four_of_card_eight_nonabelian
    {P : Type*} [Group P] [Finite P]
    (h_card : Nat.card P = 8) (h_nonab : ∃ x y : P, x * y ≠ y * x) :
    ∃ c : P, orderOf c = 4 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : IsPGroup 2 P := IsPGroup.of_card (p := 2) (n := 3) (by
    rw [h_card]
    norm_num)
  obtain ⟨c, hc_sq_ne⟩ := exists_sq_ne_one_of_nonabelian h_nonab
  obtain ⟨k, h_order⟩ := (IsPGroup.iff_orderOf.mp hP) c
  have hk_le : k ≤ 3 := by
    have hdvd : 2 ^ k ∣ 2 ^ 3 := by
      have hdvd0 : orderOf c ∣ 8 := by
        rw [← h_card]
        exact orderOf_dvd_natCard c
      rw [h_order] at hdvd0
      simpa using hdvd0
    exact (Nat.pow_dvd_pow_iff_le_right one_lt_two).mp hdvd
  have hk_two : 2 ≤ k := by
    by_contra hk_not
    have hk_cases : k = 0 ∨ k = 1 := by omega
    rcases hk_cases with rfl | rfl
    · rw [pow_zero] at h_order
      have hc_one : c = 1 := orderOf_eq_one_iff.mp h_order
      exact hc_sq_ne (by rw [hc_one, one_pow])
    · rw [pow_one] at h_order
      exact hc_sq_ne (orderOf_dvd_iff_pow_eq_one.mp (by rw [h_order]))
  have hk_ne_three : k ≠ 3 := by
    intro hk3
    have hcyc : IsCyclic P := isCyclic_of_orderOf_eq_card c (by
      rw [h_order, hk3, h_card]
      norm_num)
    obtain ⟨x, y, hxy⟩ := h_nonab
    haveI : IsCyclic P := hcyc
    exact hxy (Std.Commutative.comm x y)
  have hk_eq : k = 2 := by omega
  exact ⟨c, by rw [h_order, hk_eq]; norm_num⟩

private lemma mem_zpowers_orderOf_four_eq_self_or_inv
    {P : Type*} [Group P] [Finite P] {c y : P}
    (h_order : orderOf c = 4)
    (hy_mem : y ∈ Subgroup.zpowers c)
    (hy_order : orderOf y = 4) :
    y = c ∨ y = c⁻¹ := by
  classical
  have hy_range : y ∈ (Finset.range (orderOf c)).image (fun n : ℕ => c ^ n) :=
    (mem_zpowers_iff_mem_range_orderOf (x := c) (y := y)).mp hy_mem
  rcases Finset.mem_image.mp hy_range with ⟨m, hm_range, hm_eq⟩
  have hm_lt : m < 4 := by
    have := Finset.mem_range.mp hm_range
    rwa [h_order] at this
  have hm_cases : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 := by omega
  rcases hm_cases with rfl | rfl | rfl | rfl
  · rw [pow_zero] at hm_eq
    rw [← hm_eq, orderOf_one] at hy_order
    norm_num at hy_order
  · left
    simpa using hm_eq.symm
  · have hy_sq : y ^ 2 = 1 := by
      rw [← hm_eq, ← pow_mul]
      change c ^ 4 = 1
      rw [← h_order, pow_orderOf_eq_one]
    have hdvd : 4 ∣ 2 := by
      rw [← hy_order]
      exact orderOf_dvd_of_pow_eq_one hy_sq
    norm_num at hdvd
  · right
    rw [← hm_eq]
    have hmul : c ^ 3 * c = 1 := by
      rw [← pow_succ]
      change c ^ 4 = 1
      rw [← h_order, pow_orderOf_eq_one]
    exact eq_inv_of_mul_eq_one_left hmul

/-- **Isaacs Corollary 6.14**: A nonabelian group of order `8` is isomorphic to `D_8` or `Q_8`
(i.e., `DihedralGroup 4` or `QuaternionGroup 2` in mathlib indexing). -/
theorem dihedralOrQuaternion_of_card_eight
    {P : Type*} [Group P] [Finite P]
    (h_card : Nat.card P = 8) (h_nonab : ∃ x y : P, x * y ≠ y * x) :
    Nonempty (P ≃* DihedralGroup 4) ∨ Nonempty (P ≃* QuaternionGroup 2) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : IsPGroup 2 P := IsPGroup.of_card (p := 2) (n := 3) (by
    rw [h_card]
    norm_num)
  obtain ⟨c, h_order4⟩ :=
    exists_orderOf_eq_four_of_card_eight_nonabelian h_card h_nonab
  have h_idx : (Subgroup.zpowers c).index = 2 := by
    have h := (Subgroup.zpowers c).index_mul_card
    rw [Nat.card_zpowers, h_order4, h_card] at h
    omega
  obtain ⟨a, h_a_notmem, _h_cover⟩ :=
    (Subgroup.index_eq_two_iff_exists_notMem_and.mp h_idx)
  have h_a_inv_notmem : a⁻¹ ∉ Subgroup.zpowers c := by
    intro ha
    exact h_a_notmem ((Subgroup.zpowers c).inv_mem_iff.mp ha)
  have h_ac_notmem : a * c ∉ Subgroup.zpowers c := by
    rw [Subgroup.mul_mem_iff_of_index_two h_idx]
    intro hiff
    exact h_a_notmem (hiff.mpr (Subgroup.mem_zpowers c))
  have hy_mem : a * c * a⁻¹ ∈ Subgroup.zpowers c := by
    rw [Subgroup.mul_mem_iff_of_index_two h_idx]
    exact iff_of_false h_ac_notmem h_a_inv_notmem
  have hy_order : orderOf (a * c * a⁻¹) = 4 := by
    have hsemi : SemiconjBy a c (a * c * a⁻¹) := by
      change a * c = (a * c * a⁻¹) * a
      group
    exact (SemiconjBy.orderOf_eq a hsemi).symm.trans h_order4
  rcases mem_zpowers_orderOf_four_eq_self_or_inv h_order4 hy_mem hy_order with h_conj_fixed | h_conj
  · exfalso
    have h_comm : Commute a c := by
      change a * c = c * a
      calc a * c = (a * c * a⁻¹) * a := by group
        _ = c * a := by rw [h_conj_fixed]
    obtain ⟨x, y, hxy⟩ := h_nonab
    exact hxy (commutative_of_index_two_zpowers_of_commute_generator c a
      h_idx h_a_notmem h_comm x y)
  · rcases dihedralOrQuaternion_of_invertingConjugation hP c a h_idx h_a_notmem h_conj
      with hD | hQ
    · left
      rw [h_order4] at hD
      exact hD
    · right
      have h_half : orderOf c / 2 = 2 := by
        rw [h_order4]
      rw [h_half] at hQ
      exact hQ

/-- **Isaacs Thm 6.12, `|C| = 4` branch**: a self-centralizing normal cyclic subgroup
of order `4` in a nonabelian finite group forces the ambient group to have order `8`, so
Corollary 6.14 applies. -/
theorem dihedralOrQuaternion_of_self_centralizing_cyclic_card_four
    {P : Type*} [Group P] [Finite P]
    {C : Subgroup P} [C.Normal]
    (hC_cyclic : IsCyclic C)
    (hCent : Subgroup.centralizer (C : Set P) = C)
    (hC_card : Nat.card C = 4)
    (h_nonab : ∃ x y : P, x * y ≠ y * x) :
    Nonempty (P ≃* DihedralGroup 4) ∨ Nonempty (P ≃* QuaternionGroup 2) := by
  classical
  have hquot_le : Nat.card (P ⧸ C) ≤ Nat.card (MulAut C) :=
    quotient_card_le_mulAut_of_self_centralizing hCent
  have hmulAut_card : Nat.card (MulAut C) = 2 := by
    haveI : IsCyclic C := hC_cyclic
    rw [IsCyclic.card_mulAut, hC_card]
    decide
  have hquot_le_two : Nat.card (P ⧸ C) ≤ 2 := by
    rwa [hmulAut_card] at hquot_le
  have hC_ne_top : C ≠ ⊤ := by
    intro hC_top
    have hP_cyclic : IsCyclic P := by
      rw [← Subgroup.topEquiv.isCyclic]
      rwa [← hC_top]
    obtain ⟨x, y, hxy⟩ := h_nonab
    haveI : IsCyclic P := hP_cyclic
    exact hxy (Std.Commutative.comm x y)
  have hquot_gt_one : 1 < Nat.card (P ⧸ C) :=
    Finite.one_lt_card_iff_nontrivial.mpr
      (Subgroup.nontrivial_quotient_of_ne_top hC_ne_top)
  have hquot_card : Nat.card (P ⧸ C) = 2 := by omega
  have hP_card : Nat.card P = 8 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup C, hquot_card, hC_card]
  exact dihedralOrQuaternion_of_card_eight hP_card h_nonab


end OddOrder.Isaacs.Ch06
