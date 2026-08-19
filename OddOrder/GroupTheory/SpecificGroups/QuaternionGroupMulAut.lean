/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.SpecificGroups.Quaternion
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Fintype.Perm
import Mathlib.Logic.Equiv.Option
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Algebra.Group.End

/-!
# Odd automorphism groups of the quaternion group `Q₈`

Shared infrastructure for Peterfalvi, *Character Theory for the Odd Order
Theorem* (LMS LNS 272, 2000), Part II, Ch. II, step (6) (p. 110): "an odd order
group of automorphisms of `F_{9,2}` can only have order 1 or 3 as `F*_{9,2}` is
quaternion of order 8".

The main result is `card_dvd_three_of_odd_mulAutQuaternion`: an odd-order
subgroup of `MulAut (QuaternionGroup 2)` has order dividing `3`; the
`MulEquiv`-transported form `card_dvd_three_of_odd_mulAut_of_mulEquiv` is the
one consumed downstream (with the ambient group `Fˣ ≃* QuaternionGroup 2`).

The proof avoids computing `|Aut(Q₈)| = 24`.  The commutator subgroup of `Q₈`
is its center `{1, a 2}` (order `2`), so the abelianization has order `4`; an
automorphism acting trivially on the abelianization moves each of the
generators `a 1`, `xa 0` at most into its coset modulo `{1, a 2}`, and all four
such assignments square to the identity.  Hence the kernel of
`MulAut Q₈ → MulAut (Abelianization Q₈)` meets an odd-order subgroup trivially,
while the image embeds into the permutations of the three nonidentity elements
of the abelianization — a group of order `3! = 6`.  An odd divisor of `6`
divides `3`.
-/

namespace OddOrder.GroupTheory

open QuaternionGroup Subgroup Equiv Function

open scoped commutatorElement

/-- The functorial homomorphism `MulAut G →* MulAut (Abelianization G)`. -/
def mulAutToAbelianization (G : Type*) [Group G] :
    MulAut G →* MulAut (Abelianization G) where
  toFun f := f.abelianizationCongr
  map_one' := abelianizationCongr_refl
  map_mul' f g := (abelianizationCongr_trans g f).symm

@[simp]
theorem mulAutToAbelianization_apply_of {G : Type*} [Group G] (f : MulAut G) (x : G) :
    mulAutToAbelianization G f (Abelianization.of x) = Abelianization.of (f x) :=
  rfl

/-- Restriction of automorphisms to the permutations of the nonidentity
elements: `MulAut A →* Equiv.Perm {x : A // x ≠ 1}`. -/
def mulAutToPermNeOne (A : Type*) [Group A] :
    MulAut A →* Equiv.Perm {x : A // x ≠ 1} where
  toFun f := f.toEquiv.subtypeEquiv fun x => not_congr f.map_eq_one_iff.symm
  map_one' := by
    ext x
    simp [Equiv.subtypeEquiv]
  map_mul' f g := by
    ext x
    simp [Equiv.subtypeEquiv]

theorem mulAutToPermNeOne_injective (A : Type*) [Group A] :
    Function.Injective (mulAutToPermNeOne A) := by
  intro f g hfg
  ext x
  by_cases hx : x = 1
  · simp [hx]
  · have := congrArg (fun σ => ((σ ⟨x, hx⟩ : {x : A // x ≠ 1}) : A)) hfg
    simpa [mulAutToPermNeOne, Equiv.subtypeEquiv] using this

section QuaternionTwo

local notation "Q₈" => QuaternionGroup 2
local notation "A₈" => Abelianization (QuaternionGroup 2)

/-- Every commutator in `Q₈` lies in `{1, a 2}`. -/
private theorem commutatorElement_eq_one_or (x y : Q₈) :
    ⁅x, y⁆ = 1 ∨ ⁅x, y⁆ = a 2 := by
  revert x y
  decide

/-- The commutator subgroup of `Q₈` is `⟨a 2⟩ = {1, a 2}` (the center). -/
theorem commutator_quaternionTwo_eq :
    commutator Q₈ = zpowers (a 2) := by
  refine le_antisymm (commutator_le.mpr fun g₁ _ g₂ _ => ?_) (zpowers_le.mpr ?_)
  · rcases commutatorElement_eq_one_or g₁ g₂ with h | h <;> rw [h]
    · exact one_mem _
    · exact mem_zpowers _
  · have h : (a 2 : Q₈) = ⁅(a 1 : Q₈), xa 0⁆ := by decide
    rw [_root_.commutator_def, h]
    exact commutator_mem_commutator (mem_top _) (mem_top _)

private theorem mem_zpowers_a_two {x : Q₈} (hx : x ∈ zpowers (a 2)) :
    x = 1 ∨ x = a 2 := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hx
  have h2 : (a 2 : Q₈) ^ (2 : ℤ) = 1 := by decide
  rcases Int.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · left
    rw [← two_mul, zpow_mul, h2, one_zpow]
  · right
    rw [zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one]

/-- Two automorphisms of `Q₈` agreeing on the generators `a 1` and `xa 0` are
equal. -/
private theorem mulAut_ext_generators {f g : MulAut Q₈}
    (h1 : f (a 1) = g (a 1)) (h2 : f (xa 0) = g (xa 0)) : f = g := by
  have ha : ∀ j : ZMod (2 * 2), f (a j) = g (a j) := by
    intro j
    have hj : (a j : Q₈) = a 1 ^ j.val := by
      rw [a_one_pow]
      exact congrArg _ (ZMod.natCast_rightInverse j).symm
    rw [hj, map_pow, map_pow, h1]
  ext x
  cases x with
  | a i => exact ha i
  | xa i =>
    have hi : (xa i : Q₈) = a (-i) * xa 0 := by
      rw [a_mul_xa, sub_neg_eq_add, zero_add]
    rw [hi, map_mul, map_mul, ha, h2]

/-- An automorphism of `Q₈` acting trivially modulo the commutator subgroup
squares to the identity. -/
private theorem sq_eq_one_of_forall_mul_inv_mem_commutator (f : MulAut Q₈)
    (hf : ∀ x : Q₈, f x * x⁻¹ ∈ commutator Q₈) : f ^ 2 = 1 := by
  have key : ∀ x : Q₈, f x = x ∨ f x = a 2 * x := by
    intro x
    rcases mem_zpowers_a_two (commutator_quaternionTwo_eq ▸ hf x) with h | h
    · exact Or.inl (by rwa [mul_inv_eq_one] at h)
    · exact Or.inr (mul_inv_eq_iff_eq_mul.mp h)
  have hfa2 : f (a 2) = a 2 := by
    have h2 : (a 2 : Q₈) = a 1 ^ 2 := by decide
    rcases key (a 1) with h | h
    · rw [h2, map_pow, h]
    · rw [h2, map_pow, h]
      decide
  have hsq_a : (f ^ 2) (a 1) = (1 : MulAut Q₈) (a 1) := by
    rw [pow_two, MulAut.mul_apply, MulAut.one_apply]
    rcases key (a 1) with h | h
    · rw [h, h]
    · have h3 : (a 2 * a 1 : Q₈) = a 1 ^ 3 := by decide
      rw [h, h3, map_pow, h]
      decide
  have hsq_xa : (f ^ 2) (xa 0) = (1 : MulAut Q₈) (xa 0) := by
    rw [pow_two, MulAut.mul_apply, MulAut.one_apply]
    rcases key (xa 0) with h | h
    · rw [h, h]
    · rw [h, map_mul, hfa2, h, ← mul_assoc]
      decide
  exact mulAut_ext_generators hsq_a hsq_xa

/-- **Odd automorphism groups of `Q₈` have order dividing 3** (used through
Peterfalvi, Part II, Ch. II, step (6), p. 110).  The kernel of the action on
`Abelianization Q₈` meets an odd-order subgroup trivially
(`sq_eq_one_of_forall_mul_inv_mem_commutator`), and the image embeds into the
permutations of the three nonidentity classes. -/
theorem card_dvd_three_of_odd_mulAutQuaternion
    (D : Subgroup (MulAut Q₈)) (hodd : Odd (Nat.card D)) :
    Nat.card D ∣ 3 := by
  classical
  -- `|Abelianization Q₈| = 4`: `|Q₈| = 8`, commutator subgroup of order `2`
  have hcard_comm : Nat.card (commutator Q₈) = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [commutator_quaternionTwo_eq, Nat.card_zpowers]
    exact orderOf_eq_prime (by decide) (by decide)
  have hcard_Q8 : Nat.card Q₈ = 8 := by
    rw [Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hcard_A : Nat.card A₈ = 4 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (commutator Q₈)
    rw [hcard_Q8, hcard_comm] at h
    have hA : Nat.card A₈ = Nat.card (Q₈ ⧸ commutator Q₈) := rfl
    omega
  -- the target permutation group has order `3! = 6`
  have : Finite A₈ := Quotient.finite _
  have hcard_ne : Nat.card {x : A₈ // x ≠ 1} = 3 := by
    have h := Nat.card_congr (Equiv.optionSubtypeNe (1 : A₈))
    rw [Finite.card_option, hcard_A] at h
    omega
  have hcard_perm : Nat.card (Equiv.Perm {x : A₈ // x ≠ 1}) = 6 := by
    let : Fintype {x : A₈ // x ≠ 1} := Fintype.ofFinite _
    have h3 : Fintype.card {x : A₈ // x ≠ 1} = 3 := by
      rw [← Nat.card_eq_fintype_card]
      exact hcard_ne
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, h3]
    norm_num [Nat.factorial]
  -- the composite `D →* Perm {x : A₈ // x ≠ 1}` is injective
  set ψ : D →* Equiv.Perm {x : A₈ // x ≠ 1} :=
    ((mulAutToPermNeOne A₈).comp (mulAutToAbelianization Q₈)).comp D.subtype with hψ
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
    intro d hd
    have hψd : ψ d = 1 := MonoidHom.mem_ker.mp hd
    have hπ : mulAutToAbelianization Q₈ (d : MulAut Q₈) = 1 :=
      mulAutToPermNeOne_injective _
        (by simpa [ψ, MonoidHom.comp_apply, map_one] using hψd)
    -- trivial action on the abelianization ⟹ `d² = 1`
    have hcomm : ∀ x : Q₈, (d : MulAut Q₈) x * x⁻¹ ∈ commutator Q₈ := by
      intro x
      have hx : Abelianization.of ((d : MulAut Q₈) x) = Abelianization.of x := by
        have h := congrArg (fun g : MulAut A₈ => g (Abelianization.of x)) hπ
        simpa using h
      have h1 : Abelianization.of ((d : MulAut Q₈) x * x⁻¹) = 1 := by
        rw [map_mul, map_inv, hx, mul_inv_cancel]
      rwa [← MonoidHom.mem_ker, Abelianization.ker_of] at h1
    have hsq : ((d : MulAut Q₈)) ^ 2 = 1 :=
      sq_eq_one_of_forall_mul_inv_mem_commutator _ hcomm
    -- odd order + square one ⟹ identity
    have hd2 : d ^ 2 = 1 := Subtype.ext (by push_cast; exact hsq)
    have hdvd2 : orderOf d ∣ 2 := orderOf_dvd_of_pow_eq_one hd2
    have hodd_ord : Odd (orderOf d) := by
      rcases Nat.even_or_odd (orderOf d) with he | ho
      · exact absurd (he.two_dvd.trans (orderOf_dvd_natCard d))
          fun h2 => Nat.not_even_iff_odd.mpr hodd (even_iff_two_dvd.mpr h2)
      · exact ho
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd2 with h1 | h2
    · exact orderOf_eq_one_iff.mp h1
    · exact absurd (h2 ▸ hodd_ord) (by decide)
  -- Lagrange in the permutation group
  have hcard_range : Nat.card D = Nat.card ψ.range := by
    rw [Nat.card_congr (Equiv.ofInjective ψ hinj)]
    exact Nat.card_congr (Equiv.setCongr (MonoidHom.coe_range ψ).symm)
  have hdvd6 : Nat.card D ∣ 6 := by
    rw [hcard_range, ← hcard_perm]
    exact Subgroup.card_subgroup_dvd_card ψ.range
  -- odd divisor of `6 = 3 * 2` divides `3`
  have hnot2 : ¬ 2 ∣ Nat.card D :=
    fun h2 => Nat.not_even_iff_odd.mpr hodd (even_iff_two_dvd.mpr h2)
  have hcop : Nat.Coprime (Nat.card D) 2 :=
    Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hnot2)
  exact hcop.dvd_of_dvd_mul_right
    (show Nat.card D ∣ 3 * 2 by rwa [show (3 : ℕ) * 2 = 6 by norm_num])

/-- `MulEquiv`-transported form: a faithful odd automorphism action on a group
isomorphic to `Q₈` has order `1` or `3`.  This is the form consumed by
Peterfalvi Part II, Ch. II, step (6) with the ambient group `Fˣ` for the
near-field `F = F_{9,2}`. -/
theorem card_dvd_three_of_odd_mulAut_of_mulEquiv {Q : Type*} [Group Q]
    (e : Q ≃* QuaternionGroup 2) {D : Type*} [Group D]
    (φ : D →* MulAut Q) (hφ : Function.Injective φ) (hodd : Odd (Nat.card D)) :
    Nat.card D ∣ 3 := by
  classical
  set χ : D →* MulAut (QuaternionGroup 2) :=
    (MulAut.congr e).toMonoidHom.comp φ with hχ
  have hχinj : Function.Injective χ := (MulAut.congr e).injective.comp hφ
  have hcard : Nat.card D = Nat.card χ.range := by
    rw [Nat.card_congr (Equiv.ofInjective χ hχinj)]
    exact Nat.card_congr (Equiv.setCongr (MonoidHom.coe_range χ).symm)
  rw [hcard]
  exact card_dvd_three_of_odd_mulAutQuaternion χ.range (hcard ▸ hodd)

end QuaternionTwo

end OddOrder.GroupTheory
