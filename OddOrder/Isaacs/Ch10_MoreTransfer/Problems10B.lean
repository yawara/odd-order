/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.IsMetacyclic
import OddOrder.GroupTheory.MaschkeComplement
import OddOrder.Isaacs.Ch10_MoreTransfer.Problems10A
import Mathlib.Data.ZMod.Units
import Mathlib.Data.Nat.Totient
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.Nilpotent

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
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero (p ^ n) := ⟨pow_ne_zero n hp.ne_zero⟩
  have hsurj := ZMod.unitsMap_surjective (m := p ^ n) (n := p) (dvd_pow_self p hn.ne')
  have hcard : Nat.card ((ZMod (p ^ n))ˣ) = p ^ (n - 1) * (p - 1) := by
    have : Fintype (ZMod (p ^ n)) := ZMod.fintype _
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
      Nat.totient_prime_pow hp hn]
  have hcardp : Nat.card ((ZMod p)ˣ) = p - 1 := by
    have : Fintype (ZMod p) := ZMod.fintype _
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
theorem unitsMap_one_add_prime (hn : 0 < n) {u : (ZMod (p ^ n))ˣ}
    (hu : (u : ZMod (p ^ n)) = 1 + (p : ZMod (p ^ n))) :
    ZMod.unitsMap (dvd_pow_self p hn.ne' : p ∣ p ^ n) u = 1 := by
  refine Units.ext ?_
  rw [ZMod.unitsMap_val, hu]
  change (ZMod.castHom (dvd_pow_self p hn.ne') (ZMod p)) (1 + (p : ZMod (p ^ n))) = 1
  rw [map_add, map_one, map_natCast, ZMod.natCast_self, add_zero]

theorem orderOf_one_add_prime_dvd (hp : p.Prime) (hn : 0 < n) {u : (ZMod (p ^ n))ˣ}
    (hu : (u : ZMod (p ^ n)) = 1 + (p : ZMod (p ^ n))) : orderOf u ∣ p ^ (n - 1) :=
  orderOf_dvd_of_unitsMap_eq_one hp hn (unitsMap_one_add_prime hn hu)

/-- `ZMod (p^n) → ZMod p` の還元で `0` になる元は `p` で割り切れる. -/
theorem prime_dvd_of_castHom_eq_zero (hp : p.Prime) (hn : 0 < n) {z : ZMod (p ^ n)}
    (h : ZMod.castHom (dvd_pow_self p hn.ne' : p ∣ p ^ n) (ZMod p) z = 0) :
    (p : ZMod (p ^ n)) ∣ z := by
  have : NeZero (p ^ n) := ⟨pow_ne_zero n hp.ne_zero⟩
  rw [ZMod.castHom_apply] at h
  have hval : ((z.val : ℕ) : ZMod p) = 0 := by
    rw [ZMod.natCast_val]
    exact h
  obtain ⟨c, hc⟩ := (ZMod.natCast_eq_zero_iff _ _).mp hval
  refine ⟨(c : ZMod (p ^ n)), ?_⟩
  have : ((z.val : ℕ) : ZMod (p ^ n)) = z := ZMod.natCast_rightInverse z
  rw [← this, hc]
  push_cast
  ring

/-- **`u ≡ 1 mod p` なら `p ∣ 1 - u^j`** (`j : ℤ`). -/
theorem prime_dvd_one_sub_zpow (hp : p.Prime) (hn : 0 < n) {u : (ZMod (p ^ n))ˣ}
    (hu : ZMod.unitsMap (dvd_pow_self p hn.ne' : p ∣ p ^ n) u = 1) (j : ℤ) :
    (p : ZMod (p ^ n)) ∣ (1 - ((u ^ j : (ZMod (p ^ n))ˣ) : ZMod (p ^ n))) := by
  have : NeZero (p ^ n) := ⟨pow_ne_zero n hp.ne_zero⟩
  refine prime_dvd_of_castHom_eq_zero hp hn ?_
  have hj : ZMod.unitsMap (dvd_pow_self p hn.ne' : p ∣ p ^ n) (u ^ j) = 1 := by
    rw [map_zpow, hu, one_zpow]
  have hval : ZMod.castHom (dvd_pow_self p hn.ne' : p ∣ p ^ n) (ZMod p)
      ((u ^ j : (ZMod (p ^ n))ˣ) : ZMod (p ^ n)) = 1 := by
    have := congrArg (Units.val) hj
    rw [ZMod.unitsMap_val] at this
    simpa using this
  rw [map_sub, map_one, hval, sub_self]

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
  have : NeZero (p ^ n) := ⟨pow_ne_zero n hp.ne_zero⟩
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

/-- `N` が可換なら, 正規部分群 `inl N` の元との交換子は `inl` 成分だけで書ける:
`⁅inl y, g⁆ = inl (y · (φ (rightHom g) y)⁻¹)`.

これが下降中心列 `γ_{k+1} = ⁅γ_k, ⊤⁆` の計算の要 (右側の `g` は `rightHom g` にしか
依らない). -/
theorem commutatorElement_inl_left {N A : Type*} [CommGroup N] [Group A] {φ : A →* MulAut N}
    (y : N) (g : SemidirectProduct N A φ) :
    ⁅(SemidirectProduct.inl y : SemidirectProduct N A φ), g⁆
      = SemidirectProduct.inl (y * (φ (SemidirectProduct.rightHom g) y)⁻¹) := by
  ext
  · simp [commutatorElement_def, mul_comm, mul_assoc]
  · simp [commutatorElement_def]

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
  have : NeZero (p ^ n) := ⟨pow_ne_zero n hp.ne_zero⟩
  obtain ⟨k, _, hk⟩ := (Nat.dvd_prime_pow hp).mp (orderOf_unitAutHom_one_add_prime hp hn hu)
  refine IsPGroup.of_card (n := n + k) ?_
  rw [SemidirectProduct.card, Nat.card_zpowers, hk, pow_add]
  congr 1
  rw [Nat.card_congr (Multiplicative.toAdd (α := ZMod (p ^ n))), Nat.card_zmod]

/-! ## 下降中心列の下からの評価 -/

/-- `φ a` の作用: `a = unitAutHom m u` を `zpowers a` の元と見たとき `(ofAdd v)^a = ofAdd (u v)`. -/
theorem subtype_zpowers_unitAutHom_apply (m : ℕ) (u : (ZMod m)ˣ) (v : ZMod m) :
    (Subgroup.subtype (Subgroup.zpowers (unitAutHom m u)))
        ⟨unitAutHom m u, Subgroup.mem_zpowers _⟩ (Multiplicative.ofAdd v)
      = Multiplicative.ofAdd ((u : ZMod m) * v) := rfl

/-- **下からの評価**: `x^{p^{k+1}}` は `γ_{k+1}` (mathlib の添字) に入る. -/
theorem inl_ofAdd_pow_mem_lowerCentralSeries
    {u : (ZMod (p ^ n))ˣ} (hu : (u : ZMod (p ^ n)) = 1 + (p : ZMod (p ^ n))) (k : ℕ) :
    (SemidirectProduct.inl (Multiplicative.ofAdd ((p : ZMod (p ^ n)) ^ (k + 1))) :
        problem10B1Group (p ^ n) u)
      ∈ (⊤ : Subgroup (problem10B1Group (p ^ n) u)).lowerCentralSeries (k + 1) := by
  have hstep : ∀ v : ZMod (p ^ n),
      ((Subgroup.subtype (Subgroup.zpowers (unitAutHom (p ^ n) u)))
        ⟨unitAutHom (p ^ n) u, Subgroup.mem_zpowers _⟩ (Multiplicative.ofAdd v))
        * (Multiplicative.ofAdd v)⁻¹ = Multiplicative.ofAdd ((p : ZMod (p ^ n)) * v) := by
    intro v
    rw [subtype_zpowers_unitAutHom_apply, ← ofAdd_neg, ← ofAdd_add, hu]
    congr 1
    ring
  induction k with
  | zero =>
    rw [Subgroup.lowerCentralSeries_succ]
    have hc := commutatorElement_inr_inl
      (φ := Subgroup.subtype (Subgroup.zpowers (unitAutHom (p ^ n) u)))
      ⟨unitAutHom (p ^ n) u, Subgroup.mem_zpowers _⟩ (Multiplicative.ofAdd (1 : ZMod (p ^ n)))
    have hval : (SemidirectProduct.inl (Multiplicative.ofAdd ((p : ZMod (p ^ n)) ^ 1)) :
        problem10B1Group (p ^ n) u)
        = ⁅(SemidirectProduct.inr ⟨unitAutHom (p ^ n) u, Subgroup.mem_zpowers _⟩ :
            problem10B1Group (p ^ n) u),
          SemidirectProduct.inl (Multiplicative.ofAdd (1 : ZMod (p ^ n)))⁆ := by
      rw [hc, hstep, mul_one, pow_one]
    rw [hval]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  | succ k ih =>
    rw [Subgroup.lowerCentralSeries_succ]
    have hc := commutatorElement_inl_left
      (φ := Subgroup.subtype (Subgroup.zpowers (unitAutHom (p ^ n) u)))
      (Multiplicative.ofAdd ((p : ZMod (p ^ n)) ^ (k + 1)))
      (SemidirectProduct.inr ⟨unitAutHom (p ^ n) u, Subgroup.mem_zpowers _⟩)
    rw [SemidirectProduct.rightHom_inr] at hc
    have hmem : (⁅(SemidirectProduct.inl
        (Multiplicative.ofAdd ((p : ZMod (p ^ n)) ^ (k + 1))) : problem10B1Group (p ^ n) u),
        SemidirectProduct.inr ⟨unitAutHom (p ^ n) u, Subgroup.mem_zpowers _⟩⁆)
        ∈ ⁅(⊤ : Subgroup (problem10B1Group (p ^ n) u)).lowerCentralSeries (k + 1),
          (⊤ : Subgroup (problem10B1Group (p ^ n) u))⁆ :=
      Subgroup.commutator_mem_commutator ih (Subgroup.mem_top _)
    have hcalc : (Multiplicative.ofAdd ((p : ZMod (p ^ n)) ^ (k + 1))) *
        ((Subgroup.subtype (Subgroup.zpowers (unitAutHom (p ^ n) u)))
          ⟨unitAutHom (p ^ n) u, Subgroup.mem_zpowers _⟩
          (Multiplicative.ofAdd ((p : ZMod (p ^ n)) ^ (k + 1))))⁻¹
        = (Multiplicative.ofAdd ((p : ZMod (p ^ n)) ^ (k + 1 + 1)))⁻¹ := by
      rw [subtype_zpowers_unitAutHom_apply]
      simp only [← ofAdd_neg, ← ofAdd_add]
      congr 1
      rw [hu]
      ring
    rw [hc, hcalc] at hmem
    rw [show (SemidirectProduct.inl
          ((Multiplicative.ofAdd ((p : ZMod (p ^ n)) ^ (k + 1 + 1)))⁻¹) :
            problem10B1Group (p ^ n) u)
        = (SemidirectProduct.inl
            (Multiplicative.ofAdd ((p : ZMod (p ^ n)) ^ (k + 1 + 1))))⁻¹ from
      map_inv SemidirectProduct.inl _] at hmem
    simpa using Subgroup.inv_mem _ hmem

/-! ## 下降中心列の上からの評価 -/

/-- `ofAdd (d · v) ∈ zpowers (ofAdd v)`. -/
theorem ofAdd_mul_mem_zpowers {m : ℕ} [NeZero m] (v d : ZMod m) :
    Multiplicative.ofAdd (d * v) ∈
      Subgroup.zpowers (Multiplicative.ofAdd v) := by
  refine Subgroup.mem_zpowers_iff.mpr ⟨(d.val : ℤ), ?_⟩
  rw [← ofAdd_zsmul]
  congr 1
  rw [zsmul_eq_mul]
  congr 1
  push_cast
  exact (ZMod.natCast_rightInverse d)

/-- **上からの評価の核**: `y` の指数が `p^k` の倍数なら, どんな `g` との交換子も
`inl ⟨x^{p^{k+1}}⟩` に入る. -/
theorem commutator_inl_mem_map_zpowers (hp : p.Prime) (hn : 0 < n) {u : (ZMod (p ^ n))ˣ}
    (hu : ZMod.unitsMap (dvd_pow_self p hn.ne' : p ∣ p ^ n) u = 1) (k : ℕ)
    {y : Multiplicative (ZMod (p ^ n))} {c : ZMod (p ^ n)}
    (hy : Multiplicative.toAdd y = c * (p : ZMod (p ^ n)) ^ k)
    (g : problem10B1Group (p ^ n) u) :
    ⁅(SemidirectProduct.inl y : problem10B1Group (p ^ n) u), g⁆
      ∈ (Subgroup.zpowers (Multiplicative.ofAdd ((p : ZMod (p ^ n)) ^ (k + 1)))).map
        SemidirectProduct.inl := by
  have : NeZero (p ^ n) := ⟨pow_ne_zero n hp.ne_zero⟩
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (SemidirectProduct.rightHom g).2
  obtain ⟨d, hd⟩ := prime_dvd_one_sub_zpow hp hn hu j
  rw [commutatorElement_inl_left]
  refine Subgroup.mem_map.mpr ⟨_, ?_, rfl⟩
  have hact : (Subgroup.subtype (Subgroup.zpowers (unitAutHom (p ^ n) u)))
      (SemidirectProduct.rightHom g) y
      = Multiplicative.ofAdd (((u ^ j : (ZMod (p ^ n))ˣ) : ZMod (p ^ n)) *
          Multiplicative.toAdd y) := by
    have : (Subgroup.subtype (Subgroup.zpowers (unitAutHom (p ^ n) u)))
        (SemidirectProduct.rightHom g) = unitAutHom (p ^ n) (u ^ j) := by
      rw [map_zpow, hj]
      rfl
    rw [this]
    rfl
  rw [hact]
  have hval : y * (Multiplicative.ofAdd
      (((u ^ j : (ZMod (p ^ n))ˣ) : ZMod (p ^ n)) * Multiplicative.toAdd y))⁻¹
      = Multiplicative.ofAdd ((d * c) * (p : ZMod (p ^ n)) ^ (k + 1)) := by
    rw [← ofAdd_neg, ← ofAdd_toAdd y, ← ofAdd_add, toAdd_ofAdd]
    congr 1
    have hexp : Multiplicative.toAdd y + -(((u ^ j : (ZMod (p ^ n))ˣ) : ZMod (p ^ n)) *
        Multiplicative.toAdd y)
        = (1 - ((u ^ j : (ZMod (p ^ n))ˣ) : ZMod (p ^ n))) * Multiplicative.toAdd y := by
      ring
    rw [hexp, hd, hy, pow_succ]
    ring
  rw [hval]
  exact ofAdd_mul_mem_zpowers _ _

/-- `N` 可換なら `g · inl v · g⁻¹ = inl (φ (rightHom g) v)`. -/
theorem conj_inl {N A : Type*} [CommGroup N] [Group A] {φ : A →* MulAut N}
    (v : N) (g : SemidirectProduct N A φ) :
    g * SemidirectProduct.inl v * g⁻¹
      = SemidirectProduct.inl (φ (SemidirectProduct.rightHom g) v) := by
  ext
  · simp [mul_comm, mul_assoc]
  · simp

/-- `inl ⟨x^{p^k}⟩` は `P` の正規部分群. -/
theorem normal_map_zpowers (hp : p.Prime) {u : (ZMod (p ^ n))ˣ} (k : ℕ) :
    ((Subgroup.zpowers (Multiplicative.ofAdd ((p : ZMod (p ^ n)) ^ k))).map
      (SemidirectProduct.inl : _ →* problem10B1Group (p ^ n) u)).Normal := by
  have : NeZero (p ^ n) := ⟨pow_ne_zero n hp.ne_zero⟩
  refine ⟨fun w hw g => ?_⟩
  obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hw
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hv
  rw [conj_inl]
  refine Subgroup.mem_map.mpr ⟨_, ?_, rfl⟩
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (SemidirectProduct.rightHom g).2
  have hact : (Subgroup.subtype (Subgroup.zpowers (unitAutHom (p ^ n) u)))
      (SemidirectProduct.rightHom g) v
      = Multiplicative.ofAdd (((u ^ j : (ZMod (p ^ n))ˣ) : ZMod (p ^ n)) *
          Multiplicative.toAdd v) := by
    have hsub : (Subgroup.subtype (Subgroup.zpowers (unitAutHom (p ^ n) u)))
        (SemidirectProduct.rightHom g) = unitAutHom (p ^ n) (u ^ j) := by
      rw [map_zpow, hj]
      rfl
    rw [hsub]
    rfl
  have hvval : Multiplicative.toAdd v = (i : ZMod (p ^ n)) * (p : ZMod (p ^ n)) ^ k := by
    rw [← hi, ← ofAdd_zsmul, toAdd_ofAdd, zsmul_eq_mul]
  rw [hact, hvval, ← mul_assoc]
  exact ofAdd_mul_mem_zpowers _ _

/-- **基点**: `⁅⊤, ⊤⁆ ≤ inl⟨x^p⟩`. -/
theorem commutator_top_le_map_zpowers (hp : p.Prime) (hn : 0 < n) {u : (ZMod (p ^ n))ˣ}
    (hu : ZMod.unitsMap (dvd_pow_self p hn.ne' : p ∣ p ^ n) u = 1) :
    ⁅(⊤ : Subgroup (problem10B1Group (p ^ n) u)),
        (⊤ : Subgroup (problem10B1Group (p ^ n) u))⁆
      ≤ (Subgroup.zpowers (Multiplicative.ofAdd ((p : ZMod (p ^ n)) ^ (0 + 1)))).map
        (SemidirectProduct.inl : _ →* problem10B1Group (p ^ n) u) := by
  have : NeZero (p ^ n) := ⟨pow_ne_zero n hp.ne_zero⟩
  set K := (Subgroup.zpowers (Multiplicative.ofAdd ((p : ZMod (p ^ n)) ^ (0 + 1)))).map
    (SemidirectProduct.inl : _ →* problem10B1Group (p ^ n) u) with hK
  have : K.Normal := by
    rw [hK]
    exact normal_map_zpowers hp _
  have hkey : ∀ (y : Multiplicative (ZMod (p ^ n))) (w : problem10B1Group (p ^ n) u),
      ⁅(SemidirectProduct.inl y : problem10B1Group (p ^ n) u), w⁆ ∈ K := fun y w =>
    commutator_inl_mem_map_zpowers hp hn hu 0 (c := Multiplicative.toAdd y) (by simp) w
  have habel : ∀ b c : ↥(Subgroup.zpowers (unitAutHom (p ^ n) u)), b * c = c * b := by
    intro b c
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp b.2
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp c.2
    refine Subtype.ext ?_
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hi, ← hj, ← zpow_add, ← zpow_add, add_comm]
  have hinr : ∀ (b : ↥(Subgroup.zpowers (unitAutHom (p ^ n) u)))
      (w : problem10B1Group (p ^ n) u),
      ⁅(SemidirectProduct.inr b : problem10B1Group (p ^ n) u), w⁆ ∈ K := by
    intro b w
    rw [show w = SemidirectProduct.inl w.left * SemidirectProduct.inr w.right from
      (SemidirectProduct.inl_left_mul_inr_right w).symm,
      commutatorElement_mul_right_eq_mul_conj]
    have h2 : ⁅(SemidirectProduct.inr b : problem10B1Group (p ^ n) u),
        (SemidirectProduct.inr w.right : problem10B1Group (p ^ n) u)⁆ = 1 := by
      rw [← map_commutatorElement (SemidirectProduct.inr :
        ↥(Subgroup.zpowers (unitAutHom (p ^ n) u)) →* problem10B1Group (p ^ n) u),
        commutatorElement_def, habel b w.right]
      simp
    rw [h2, mul_one, mul_inv_cancel_right, ← commutatorElement_inv]
    exact K.inv_mem (hkey _ _)
  rw [Subgroup.commutator_le]
  intro g _ h _
  rw [show g = SemidirectProduct.inl g.left * SemidirectProduct.inr g.right from
    (SemidirectProduct.inl_left_mul_inr_right g).symm,
    commutatorElement_mul_left_eq_conj_mul]
  exact K.mul_mem (‹K.Normal›.conj_mem _ (hinr _ _) _) (hkey _ _)

/-- **上からの評価**: `γ_{k+1} ≤ inl⟨x^{p^{k+1}}⟩`. -/
theorem lowerCentralSeries_le_map_zpowers (hp : p.Prime) (hn : 0 < n) {u : (ZMod (p ^ n))ˣ}
    (hu : ZMod.unitsMap (dvd_pow_self p hn.ne' : p ∣ p ^ n) u = 1) (k : ℕ) :
    (⊤ : Subgroup (problem10B1Group (p ^ n) u)).lowerCentralSeries (k + 1)
      ≤ (Subgroup.zpowers (Multiplicative.ofAdd ((p : ZMod (p ^ n)) ^ (k + 1)))).map
        (SemidirectProduct.inl : _ →* problem10B1Group (p ^ n) u) := by
  induction k with
  | zero =>
    rw [Subgroup.lowerCentralSeries_succ]
    exact commutator_top_le_map_zpowers hp hn hu
  | succ k ih =>
    rw [Subgroup.lowerCentralSeries_succ, Subgroup.commutator_le]
    intro w hw g _
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp (ih hw)
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hv
    refine commutator_inl_mem_map_zpowers hp hn hu (k + 1)
      (c := (i : ZMod (p ^ n))) ?_ g
    rw [← hi, ← ofAdd_zsmul, toAdd_ofAdd, zsmul_eq_mul]

/-! ## Isaacs Problem 10B.1 の結論 -/

/-- **Isaacs Problem 10B.1** (書籍 p. 312) ⭐: `C = C_{p^n}` と `a : x ↦ x^{p+1}` について
`P = C ⋊ ⟨a⟩` は **冪零類 `n`** の metacyclic `p`-群. -/
theorem nilpotencyClass_problem10B1 (hp : p.Prime) (hn : 0 < n) {u : (ZMod (p ^ n))ˣ}
    (hu : (u : ZMod (p ^ n)) = 1 + (p : ZMod (p ^ n))) :
    Group.nilpotencyClass (problem10B1Group (p ^ n) u) = n := by
  have : NeZero (p ^ n) := ⟨pow_ne_zero n hp.ne_zero⟩
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (problem10B1Group (p ^ n) u) :=
    Finite.of_equiv _ (SemidirectProduct.equivProd (φ :=
      Subgroup.subtype (Subgroup.zpowers (unitAutHom (p ^ n) u)))).symm
  have : Group.IsNilpotent (problem10B1Group (p ^ n) u) :=
    (isPGroup_problem10B1 hp hn hu).isNilpotent
  have hu' := unitsMap_one_add_prime hn hu
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  -- 上から: `γ_{m+1} = ⊥`
  have hbot : (⊤ : Subgroup (problem10B1Group (p ^ (m + 1)) u)).lowerCentralSeries (m + 1)
      = ⊥ := by
    refine le_bot_iff.mp ((lowerCentralSeries_le_map_zpowers hp hn hu' m).trans ?_)
    have hzero : ((p : ZMod (p ^ (m + 1))) ^ (m + 1)) = 0 := by
      rw [← Nat.cast_pow, ZMod.natCast_self]
    rw [hzero]
    simp
  -- 下から: `γ_m ≠ ⊥`
  have : Fact (1 < p ^ (m + 1)) := ⟨Nat.one_lt_pow (by omega) hp.one_lt⟩
  have : Nontrivial (problem10B1Group (p ^ (m + 1)) u) :=
    (SemidirectProduct.inl_injective (N := Multiplicative (ZMod (p ^ (m + 1))))
      (φ := Subgroup.subtype (Subgroup.zpowers (unitAutHom (p ^ (m + 1)) u)))).nontrivial
  have hne : (⊤ : Subgroup (problem10B1Group (p ^ (m + 1)) u)).lowerCentralSeries m ≠ ⊥ := by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · exact top_ne_bot
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    intro h
    have hmem := inl_ofAdd_pow_mem_lowerCentralSeries (p := p) (n := m' + 1 + 1) hu m'
    rw [h, Subgroup.mem_bot] at hmem
    have h1 : (Multiplicative.ofAdd ((p : ZMod (p ^ (m' + 1 + 1))) ^ (m' + 1))) = 1 :=
      SemidirectProduct.inl_injective (by simpa using hmem)
    have h2 : (((p ^ (m' + 1) : ℕ) : ZMod (p ^ (m' + 1 + 1)))) = 0 := by
      rw [Nat.cast_pow]
      simpa using congrArg Multiplicative.toAdd h1
    have hdvd := (ZMod.natCast_eq_zero_iff _ _).mp h2
    have := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp hdvd
    omega
  refine le_antisymm ?_ ?_
  · exact Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mp hbot
  · by_contra hlt
    exact hne (Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mpr (by omega))

end

section /- 10B.2: 基本可換な正規部分群は socle に入る (p. 312) -/

open OddOrder.GroupTheory

open scoped IsMulCommutative in
/-- **Isaacs Problem 10B.2** (書籍 p. 312) ⭐: `E ◁ G` が基本可換 `p`-群で
`p ∤ |G : C_G(E)|` なら `E ≤ Soc(G)`.

`Additive ↥E` を `𝔽ₚ`-加群と見て共役作用の表現 (`conjQuotientLinear`) を取り、
`Soc(G) ⊓ E` に対応する部分加群に Maschke (`exists_isCompl_invariant`) を当てて
`G`-不変な補元を得る。あとは骨格 `le_socle_of_exists_normal_complement`。 -/
theorem le_socle_of_module_of_not_dvd_index {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {E : Subgroup G} [E.Normal] [IsMulCommutative ↥E]
    [Module (ZMod p) (Additive ↥E)]
    (hidx : ¬ p ∣ (Subgroup.centralizer (E : Set G)).index) :
    E ≤ Ch02.socle G := by
  classical
  have : NeZero ((Nat.card (G ⧸ Subgroup.centralizer (E : Set G)) : ZMod p)) :=
    ⟨fun h => hidx ((ZMod.natCast_eq_zero_iff _ _).mp h)⟩
  set S : Subgroup ↥E := (Ch02.socle G ⊓ E).subgroupOf E with hS
  have hWinv : ∀ q : G ⧸ Subgroup.centralizer (E : Set G), ∀ ⦃v : Additive ↥E⦄,
      v ∈ subgroupOrderIsoSubmodule (n := p) S →
      conjQuotientLinear (n := p) q v ∈ subgroupOrderIsoSubmodule (n := p) S := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H g =>
      intro v hv
      exact conj_invariant_subgroupOf (M := Ch02.socle G ⊓ E) g (Additive.toMul v) hv
  obtain ⟨W', hW'inv, hcompl⟩ :=
    exists_isCompl_invariant (conjQuotientLinear (n := p) (N := E) (G := G)) _ hWinv
  set T : Subgroup ↥E := (subgroupOrderIsoSubmodule (n := p)).symm W' with hT
  have hcomplST : IsCompl S T := by
    have h := (subgroupOrderIsoSubmodule (n := p) (E := ↥E)).symm.isCompl hcompl
    rwa [OrderIso.symm_apply_apply] at h
  have hmapS : S.map E.subtype = Ch02.socle G ⊓ E :=
    Subgroup.map_subgroupOf_eq_of_le inf_le_right
  refine le_socle_of_exists_normal_complement
    ⟨T.map E.subtype, ?_, Subgroup.map_subtype_le T, ?_, ?_⟩
  · refine normal_map_subtype_of_conj_invariant ?_
    intro g x hx
    exact hW'inv (QuotientGroup.mk g) hx
  · refine le_bot_iff.mp ?_
    rintro x ⟨hx1, hx2⟩
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hx2
    have hsS : t ∈ S := by
      rw [hS, Subgroup.mem_subgroupOf]
      exact hx1
    have hmem : t ∈ S ⊓ T := ⟨hsS, ht⟩
    rw [disjoint_iff.mp hcomplST.disjoint, Subgroup.mem_bot] at hmem
    rw [hmem]
    simp
  · rw [← hmapS, ← Subgroup.map_sup, (codisjoint_iff.mp hcomplST.codisjoint),
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]

open scoped IsMulCommutative in
/-- **Isaacs Problem 10B.2** (書籍 p. 312) ⭐ (指数条件の形): `E ◁ G` が指数 `p` の
可換群で `p ∤ |G : C_G(E)|` なら `E ≤ Soc(G)`. -/
theorem le_socle_of_isElementaryAbelian_of_not_dvd_index {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {E : Subgroup G} [E.Normal] [IsMulCommutative ↥E]
    (hexp : ∀ x : ↥E, x ^ p = 1)
    (hidx : ¬ p ∣ (Subgroup.centralizer (E : Set G)).index) :
    E ≤ Ch02.socle G := by
  let : Module (ZMod p) (Additive ↥E) := zmodModule_of_pow_eq_one (n := p) hexp
  exact le_socle_of_module_of_not_dvd_index hidx

end

end OddOrder.Isaacs.Ch10
