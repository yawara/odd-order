/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.IsMetacyclic
import Mathlib.Data.ZMod.Units
import Mathlib.Data.Nat.Totient
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.PGroup

/-!
# Isaacs, Finite Group Theory — Problems 10B (書籍 p. 312)

> **10B.1.** Given a prime `p` and an integer `n > 0`, let `C = ⟨x⟩` be a cyclic group of
> order `p^n`.  Let `a ∈ Aut(C)` with `x^a = x^{p+1}`, and let `P = C ⋊ ⟨a⟩`.  Show that
> `P` is a metacyclic `p`-group with nilpotence class `n`.  *Hint.* Use Theorem 4.7.

本 leaf は 10B.1 の部品を積む。第一段の「metacyclic」は
`OddOrder.GroupTheory.isMetacyclic_semidirectProduct` (巡回群同士の半直積は metacyclic)。

`p`-群性の核心は **`1 + p` の `(ZMod (p^n))ˣ` での位数が `p` 冪**であること:
`1 + p` は還元写像 `(ZMod (p^n))ˣ → (ZMod p)ˣ` の核に入り, その核の位数は
`φ(p^n) / (p - 1) = p^{n-1}`。

## Main results

* `OddOrder.Isaacs.Ch10.orderOf_dvd_of_unitsMap_eq_one` — 還元の核の元は位数が
  `p^{n-1}` を割る。
* `OddOrder.Isaacs.Ch10.orderOf_one_add_prime_dvd` — `1 + p` の位数は `p^{n-1}` を割る。
-/

set_option autoImplicit false

namespace OddOrder.Isaacs.Ch10

open scoped commutatorElement

section /- 10B.1: `(ZMod (p^n))ˣ` の `1`-単位群は `p`-群 (p. 312) -/

variable {p n : ℕ}

/-- 還元写像 `(ZMod (p^n))ˣ → (ZMod p)ˣ` の核の位数は `p^{n-1}`. -/
theorem card_ker_unitsMap (hp : p.Prime) (hn : 0 < n) :
    Nat.card ↥(ZMod.unitsMap (dvd_pow_self p hn.ne' : p ∣ p ^ n)).ker = p ^ (n - 1) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero n hp.ne_zero⟩
  have hsurj := ZMod.unitsMap_surjective (m := p ^ n) (n := p) (dvd_pow_self p hn.ne')
  have hcard : Nat.card ((ZMod (p ^ n))ˣ) = p ^ (n - 1) * (p - 1) := by
    haveI : Fintype (ZMod (p ^ n)) := ZMod.fintype _
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
      Nat.totient_prime_pow hp hn]
  have hcardp : Nat.card ((ZMod p)ˣ) = p - 1 := by
    haveI : Fintype (ZMod p) := ZMod.fintype _
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime hp]
  have hquot : Nat.card ((ZMod (p ^ n))ˣ ⧸
      (ZMod.unitsMap (dvd_pow_self p hn.ne' : p ∣ p ^ n)).ker) = p - 1 := by
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _ hsurj).toEquiv, hcardp]
  have hmul := Subgroup.card_mul_index
    (ZMod.unitsMap (dvd_pow_self p hn.ne' : p ∣ p ^ n)).ker
  rw [show (ZMod.unitsMap (dvd_pow_self p hn.ne' : p ∣ p ^ n)).ker.index = p - 1 from hquot,
    hcard] at hmul
  have hp1 : 0 < p - 1 := by have := hp.two_le; omega
  exact Nat.eq_of_mul_eq_mul_right hp1 hmul

/-- 還元が `1` になる単元の位数は `p^{n-1}` を割る. -/
theorem orderOf_dvd_of_unitsMap_eq_one (hp : p.Prime) (hn : 0 < n)
    {u : (ZMod (p ^ n))ˣ}
    (hu : ZMod.unitsMap (dvd_pow_self p hn.ne' : p ∣ p ^ n) u = 1) :
    orderOf u ∣ p ^ (n - 1) := by
  have hmem : u ∈ (ZMod.unitsMap (dvd_pow_self p hn.ne' : p ∣ p ^ n)).ker :=
    MonoidHom.mem_ker.mpr hu
  have hd := orderOf_dvd_natCard (⟨u, hmem⟩ :
    ↥(ZMod.unitsMap (dvd_pow_self p hn.ne' : p ∣ p ^ n)).ker)
  rw [card_ker_unitsMap hp hn] at hd
  simpa using hd

/-- **`1 + p` の `(ZMod (p^n))ˣ` での位数は `p^{n-1}` を割る** (だから `p` 冪). -/
theorem orderOf_one_add_prime_dvd (hp : p.Prime) (hn : 0 < n) {u : (ZMod (p ^ n))ˣ}
    (hu : (u : ZMod (p ^ n)) = 1 + (p : ZMod (p ^ n))) : orderOf u ∣ p ^ (n - 1) := by
  refine orderOf_dvd_of_unitsMap_eq_one hp hn ?_
  refine Units.ext ?_
  rw [ZMod.unitsMap_val, hu]
  change (ZMod.castHom (dvd_pow_self p hn.ne') (ZMod p)) (1 + (p : ZMod (p ^ n))) = 1
  rw [map_add, map_one, map_natCast, ZMod.natCast_self, add_zero]

/-! ## 単元が定める巡回群の自己同型 -/

/-- 単元 `u : (ZMod m)ˣ` が定める `Multiplicative (ZMod m)` の自己同型 (`x ↦ x^u`).

`(ZMod m)ˣ →* MulAut (Multiplicative (ZMod m))` としてまとめる. -/
def unitAutHom (m : ℕ) : (ZMod m)ˣ →* MulAut (Multiplicative (ZMod m)) where
  toFun u :=
    { toFun := fun v => Multiplicative.ofAdd ((u : ZMod m) * Multiplicative.toAdd v)
      invFun := fun v =>
        Multiplicative.ofAdd (((u⁻¹ : (ZMod m)ˣ) : ZMod m) * Multiplicative.toAdd v)
      left_inv := fun v => by simp [← mul_assoc, u.inv_mul]
      right_inv := fun v => by simp [← mul_assoc, u.mul_inv]
      map_mul' := fun a b => by simp [← ofAdd_add, mul_add] }
  map_one' := by ext v; simp
  map_mul' u u' := by ext v; simp [MulAut.mul_apply, mul_assoc]

@[simp]
theorem unitAutHom_apply (m : ℕ) (u : (ZMod m)ˣ) (v : Multiplicative (ZMod m)) :
    unitAutHom m u v = Multiplicative.ofAdd ((u : ZMod m) * Multiplicative.toAdd v) := rfl

/-- `unitAutHom` は単射 (`ofAdd 1` での値が `u` を決める). -/
theorem unitAutHom_injective (m : ℕ) [NeZero m] : Function.Injective (unitAutHom m) := by
  intro u u' h
  have hv := congrArg (fun φ : MulAut (Multiplicative (ZMod m)) =>
    Multiplicative.toAdd (φ (Multiplicative.ofAdd 1))) h
  simp only [unitAutHom_apply, toAdd_ofAdd, mul_one] at hv
  exact Units.ext hv

/-- 単元が定める自己同型の位数は単元の位数. -/
theorem orderOf_unitAutHom (m : ℕ) [NeZero m] (u : (ZMod m)ˣ) :
    orderOf (unitAutHom m u) = orderOf u :=
  orderOf_injective (unitAutHom m) (unitAutHom_injective m) u

/-- **`1 + p` が定める `C_{p^n}` の自己同型の位数は `p` 冪**. -/
theorem orderOf_unitAutHom_one_add_prime (hp : p.Prime) (hn : 0 < n) {u : (ZMod (p ^ n))ˣ}
    (hu : (u : ZMod (p ^ n)) = 1 + (p : ZMod (p ^ n))) :
    orderOf (unitAutHom (p ^ n) u) ∣ p ^ (n - 1) := by
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero n hp.ne_zero⟩
  rw [orderOf_unitAutHom]
  exact orderOf_one_add_prime_dvd hp hn hu

/-! ## 半直積の交換子 -/

/-- 半直積での基本交換子: `⁅inr g, inl x⁆ = inl (φ g x · x⁻¹)`.

`SemidirectProduct.inl_aut` (`inl (φ g x) = inr g * inl x * inr g⁻¹`) の言い換え。 -/
theorem commutatorElement_inr_inl {N A : Type*} [Group N] [Group A] {φ : A →* MulAut N}
    (g : A) (x : N) :
    ⁅(SemidirectProduct.inr g : SemidirectProduct N A φ),
        (SemidirectProduct.inl x : SemidirectProduct N A φ)⁆
      = SemidirectProduct.inl (φ g x * x⁻¹) := by
  have key : (SemidirectProduct.inr g : SemidirectProduct N A φ) * SemidirectProduct.inl x *
      (SemidirectProduct.inr g)⁻¹ = SemidirectProduct.inl (φ g x) := by
    rw [← map_inv]
    exact (SemidirectProduct.inl_aut g x).symm
  rw [commutatorElement_def, key, ← map_inv, ← map_mul]

/-! ## Isaacs 10B.1 の群 `P = C ⋊ ⟨a⟩` -/

/-- **Isaacs Problem 10B.1 の群**: `C = C_{p^n}` と単元 `u` の定める自己同型
`a : x ↦ x^u` について `P = C ⋊ ⟨a⟩`. -/
abbrev problem10B1Group (m : ℕ) (u : (ZMod m)ˣ) : Type :=
  SemidirectProduct (Multiplicative (ZMod m))
    ↥(Subgroup.zpowers (unitAutHom m u)) (Subgroup.subtype _)

/-- **10B.1 の "metacyclic"**: `C` も `⟨a⟩` も巡回なので半直積は metacyclic. -/
theorem isMetacyclic_problem10B1 (m : ℕ) (u : (ZMod m)ˣ) :
    OddOrder.GroupTheory.IsMetacyclic (problem10B1Group m u) :=
  OddOrder.GroupTheory.isMetacyclic_semidirectProduct _

/-- **10B.1 の "`p`-群"**: `|P| = p^n · orderOf a` で `orderOf a ∣ p^{n-1}`. -/
theorem isPGroup_problem10B1 (hp : p.Prime) (hn : 0 < n) {u : (ZMod (p ^ n))ˣ}
    (hu : (u : ZMod (p ^ n)) = 1 + (p : ZMod (p ^ n))) :
    IsPGroup p (problem10B1Group (p ^ n) u) := by
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero n hp.ne_zero⟩
  obtain ⟨k, _, hk⟩ := (Nat.dvd_prime_pow hp).mp (orderOf_unitAutHom_one_add_prime hp hn hu)
  refine IsPGroup.of_card (n := n + k) ?_
  rw [SemidirectProduct.card, Nat.card_zpowers, hk, pow_add]
  congr 1
  rw [Nat.card_congr (Multiplicative.toAdd (α := ZMod (p ^ n))), Nat.card_zmod]

end

end OddOrder.Isaacs.Ch10
