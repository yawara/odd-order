/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.FiniteAbelian.Basic
import OddOrder.GroupTheory.OmegaSubgroup

/-!
# Homocyclic finite abelian 2-groups

This file isolates the homogeneous cyclic-factor argument from Graham Higman,
*Suzuki 2-groups*, Illinois J. Math. 7 (1963), Lemma 1, p. 83.

If every involution of a finite abelian `2`-group has the same height in the
power filtration, the finite abelian decomposition cannot contain cyclic
factors of different orders.  The main theorem below makes this argument
explicit using the `Agemo` filtration.
-/

set_option autoImplicit false

namespace OddOrder.GroupTheory

/-- **Higman, Suzuki 2-groups, Lemma 1 — homogeneous-factor part**: a finite
abelian `2`-group whose involutions all have the same Agemo height is a direct
product of cyclic groups of one common order `2 ^ e`.

The index type may be empty, covering the trivial group; in that case we take
`e = 1`. -/
theorem exists_homocyclic_decomposition_of_involution_heights
    {A : Type*} [CommGroup A] [Finite A]
    (hA : IsPGroup 2 A)
    (hheight : ∀ x y : A, orderOf x = 2 → orderOf y = 2 → ∀ s : ℕ,
      (x ∈ Agemo A 2 s ↔ y ∈ Agemo A 2 s)) :
    ∃ (ι : Type) (_ : Fintype ι) (e : ℕ), 0 < e ∧
      Nonempty (A ≃* ((i : ι) → Multiplicative (ZMod (2 ^ e)))) := by
  classical
  obtain ⟨ι, hι, n, hn_gt, ⟨ε⟩⟩ :=
    CommGroup.equiv_prod_multiplicative_zmod_of_finite A
  letI : Fintype ι := hι
  let B := (i : ι) → Multiplicative (ZMod (n i))
  have hB : IsPGroup 2 B := hA.of_equiv ε
  have hn_pow : ∀ i : ι, ∃ m : ℕ, 0 < m ∧ n i = 2 ^ m := by
    intro i
    let g : B := Pi.mulSingle i (.ofAdd 1)
    have hgord : orderOf g = n i := by
      simp [g, B, orderOf_piMulSingle, orderOf_ofAdd_eq_addOrderOf,
        ZMod.addOrderOf_one]
    obtain ⟨k, hk⟩ := hB g
    obtain ⟨m, _hmk, hm⟩ :=
      (Nat.dvd_prime_pow Nat.prime_two).mp
        (show n i ∣ 2 ^ k by rw [← hgord]; exact orderOf_dvd_of_pow_eq_one hk)
    have hmpos : 0 < m := by
      by_contra hm0
      have : m = 0 := Nat.eq_zero_of_not_pos hm0
      subst m
      have hgt := hn_gt i
      simp at hm
      omega
    exact ⟨m, hmpos, hm⟩
  choose m hmpos hn using hn_pow
  have hgen_order (i : ι) :
      orderOf (Pi.mulSingle i (.ofAdd 1) : B) = 2 ^ m i := by
    simpa [B, orderOf_piMulSingle, orderOf_ofAdd_eq_addOrderOf,
      ZMod.addOrderOf_one] using hn i
  let t : ι → B := fun i =>
    (Pi.mulSingle i (.ofAdd 1) : B) ^ (2 ^ (m i - 1))
  have ht_order (i : ι) : orderOf (t i) = 2 := by
    change orderOf ((Pi.mulSingle i (.ofAdd 1) : B) ^ (2 ^ (m i - 1))) = 2
    have htwo_dvd : 2 ∣ orderOf (Pi.mulSingle i (.ofAdd 1) : B) := by
      rw [hgen_order i]
      exact dvd_pow_self 2 (Nat.ne_of_gt (hmpos i))
    have hord_ne : orderOf (Pi.mulSingle i (.ofAdd 1) : B) ≠ 0 := by
      rw [hgen_order i]
      positivity
    have hexp : orderOf (Pi.mulSingle i (.ofAdd 1) : B) / 2 = 2 ^ (m i - 1) := by
      rw [hgen_order i]
      exact (Nat.pow_sub_one (by norm_num) (Nat.ne_of_gt (hmpos i))).symm
    rw [← hexp]
    exact orderOf_pow_orderOf_div hord_ne htwo_dvd
  have hm_eq : ∀ i j : ι, m i = m j := by
    intro i j
    apply le_antisymm
    · by_contra hnot
      have hji : m j < m i := Nat.lt_of_not_ge hnot
      let xi : A := ε.symm (t i)
      let xj : A := ε.symm (t j)
      have hxi_order : orderOf xi = 2 := by
        simpa [xi] using ht_order i
      have hxj_order : orderOf xj = 2 := by
        simpa [xj] using ht_order j
      have hxi_agemo : xi ∈ Agemo A 2 (m i - 1) := by
        rw [mem_agemo_iff_of_comm]
        refine ⟨ε.symm (Pi.mulSingle i (.ofAdd 1) : B), ?_⟩
        simp [xi, t]
      have hxj_agemo : xj ∈ Agemo A 2 (m i - 1) :=
        (hheight xi xj hxi_order hxj_order (m i - 1)).mp hxi_agemo
      obtain ⟨y, hy⟩ := mem_agemo_iff_of_comm.mp hxj_agemo
      have hyB : t j = (ε y) ^ (2 ^ (m i - 1)) := by
        apply ε.symm.injective
        simpa [xj] using hy
      have hyj := congrFun hyB j
      have hpow_one : ((ε y) j) ^ (2 ^ (m i - 1)) = 1 := by
        rw [← orderOf_dvd_iff_pow_eq_one]
        refine (orderOf_dvd_natCard ((ε y) j)).trans ?_
        simpa [hn j] using pow_dvd_pow 2 (show m j ≤ m i - 1 by omega)
      have htj_one : t j = 1 := by
        funext k
        by_cases hkj : k = j
        · subst k
          calc
            t j j = ((ε y) ^ (2 ^ (m i - 1))) j := hyj
            _ = ((ε y) j) ^ (2 ^ (m i - 1)) := rfl
            _ = 1 := hpow_one
            _ = (1 : B) j := rfl
        · change ((Pi.mulSingle j (.ofAdd 1) : B) k) ^ (2 ^ (m j - 1)) = 1
          rw [Pi.mulSingle_eq_of_ne hkj, one_pow]
      have hcontra := ht_order j
      rw [htj_one, orderOf_one] at hcontra
      omega
    · by_contra hnot
      have hij : m i < m j := Nat.lt_of_not_ge hnot
      let xi : A := ε.symm (t i)
      let xj : A := ε.symm (t j)
      have hxi_order : orderOf xi = 2 := by simpa [xi] using ht_order i
      have hxj_order : orderOf xj = 2 := by simpa [xj] using ht_order j
      have hxj_agemo : xj ∈ Agemo A 2 (m j - 1) := by
        rw [mem_agemo_iff_of_comm]
        refine ⟨ε.symm (Pi.mulSingle j (.ofAdd 1) : B), ?_⟩
        simp [xj, t]
      have hxi_agemo : xi ∈ Agemo A 2 (m j - 1) :=
        (hheight xj xi hxj_order hxi_order (m j - 1)).mp hxj_agemo
      obtain ⟨y, hy⟩ := mem_agemo_iff_of_comm.mp hxi_agemo
      have hyB : t i = (ε y) ^ (2 ^ (m j - 1)) := by
        apply ε.symm.injective
        simpa [xi] using hy
      have hyi := congrFun hyB i
      have hpow_one : ((ε y) i) ^ (2 ^ (m j - 1)) = 1 := by
        rw [← orderOf_dvd_iff_pow_eq_one]
        refine (orderOf_dvd_natCard ((ε y) i)).trans ?_
        simpa [hn i] using pow_dvd_pow 2 (show m i ≤ m j - 1 by omega)
      have hti_one : t i = 1 := by
        funext k
        by_cases hki : k = i
        · subst k
          calc
            t i i = ((ε y) ^ (2 ^ (m j - 1))) i := hyi
            _ = ((ε y) i) ^ (2 ^ (m j - 1)) := rfl
            _ = 1 := hpow_one
            _ = (1 : B) i := rfl
        · change ((Pi.mulSingle i (.ofAdd 1) : B) k) ^ (2 ^ (m i - 1)) = 1
          rw [Pi.mulSingle_eq_of_ne hki, one_pow]
      have hcontra := ht_order i
      rw [hti_one, orderOf_one] at hcontra
      omega
  let e : ℕ := max 1 (Finset.univ.sup m)
  have hepos : 0 < e := by simp [e]
  have hne : ∀ i : ι, n i = 2 ^ e := by
    intro i
    rw [hn i]
    congr 1
    have hsup_le : Finset.univ.sup m ≤ m i := by
      apply Finset.sup_le
      intro j _
      exact (hm_eq j i).le
    have hmi_le_sup : m i ≤ Finset.univ.sup m :=
      Finset.le_sup (f := m) (Finset.mem_univ i)
    have hsup : Finset.univ.sup m = m i := le_antisymm hsup_le hmi_le_sup
    have hmone : 1 ≤ m i := hmpos i
    simp [e, hsup, hmone]
  let δ : ((i : ι) → Multiplicative (ZMod (n i))) ≃*
      ((i : ι) → Multiplicative (ZMod (2 ^ e))) :=
    MulEquiv.piCongrRight fun i =>
      MulEquiv.toAdditive.symm (ZMod.ringEquivCongr (hne i)).toAddEquiv
  exact ⟨ι, hι, e, hepos, ⟨ε.trans δ⟩⟩

end OddOrder.GroupTheory
