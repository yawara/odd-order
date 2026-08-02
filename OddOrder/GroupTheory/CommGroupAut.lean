/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.ElementaryAbelianLinear
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.Exponent
import Mathlib.Data.ZMod.Units

/-!
# The automorphism group of a commutative group

Two general constraints on `Aut(A)` for a commutative group `A`, both needed for the
classification of the abelian groups with simple automorphism group (Isaacs Problem 8C.6):

* inversion `a ↦ a⁻¹` is a *central* automorphism, so if `Aut(A)` is simple and `A` has
  exponent bigger than `2` then `Aut(A)` is forced to be the group of order `2`;
* the power maps `a ↦ a ^ k` for `k` prime to the exponent `n` embed `(ZMod n)ˣ` into
  `Aut(A)`, so `φ(n) ≤ |Aut(A)|`.

Together: a finite abelian `A` with simple `Aut(A)` and an element of order `> 2` has
`φ(exp A) ≤ 2`, i.e. `exp A ∈ {3, 4, 6}`.

## Main results

* `OddOrder.GroupTheory.invMulAut` — inversion as an automorphism, with
  `invMulAut_mem_center`.
* `OddOrder.GroupTheory.card_mulAut_eq_two_of_isSimpleGroup`
* `OddOrder.GroupTheory.totient_exponent_le_card_mulAut`
-/

set_option autoImplicit false

namespace OddOrder.GroupTheory

variable {A : Type*} [CommGroup A]

/-! ## Inversion is a central automorphism -/

/-- 可換群 `A` の反転写像 `a ↦ a⁻¹` は自己同型. -/
def invMulAut (A : Type*) [CommGroup A] : MulAut A where
  toFun a := a⁻¹
  invFun a := a⁻¹
  left_inv := inv_inv
  right_inv := inv_inv
  map_mul' a b := mul_inv a b

@[simp]
theorem invMulAut_apply (a : A) : invMulAut A a = a⁻¹ := rfl

/-- 反転はすべての自己同型と可換 — 自己同型は逆元を保つから. -/
theorem invMulAut_mem_center : invMulAut A ∈ Subgroup.center (MulAut A) := by
  rw [Subgroup.mem_center_iff]
  intro g
  ext a
  simp [MulAut.mul_apply]

@[simp]
theorem invMulAut_sq : invMulAut A * invMulAut A = 1 := by
  ext a
  simp [MulAut.mul_apply]

/-- 反転が自明 ⟺ `A` の指数が `2` を割る. -/
theorem invMulAut_eq_one_iff : invMulAut A = 1 ↔ ∀ a : A, a ^ 2 = 1 := by
  constructor
  · intro h a
    have hinv : a⁻¹ = a := by
      have := congrArg (fun f : MulAut A => f a) h
      simpa using this
    calc a ^ 2 = a * a := pow_two a
      _ = a⁻¹ * a := by rw [hinv]
      _ = 1 := inv_mul_cancel a
  · intro h
    ext a
    have : a * a = 1 := by simpa [pow_two] using h a
    simpa using inv_eq_of_mul_eq_one_left this

/-- **可換群 `A` の自己同型群が単純で `A` の指数が `2` より大きいなら `|Aut(A)| = 2`.**

反転 `a ↦ a⁻¹` は `Aut(A)` の中心元 (`invMulAut_mem_center`) なので, 単純性から中心は
`⊤`, すなわち `Aut(A)` は可換. 可換な単純群は素数位数 (`Group.is_simple_iff_prime_card`)
で, 位数 `2` の元 (反転) をもつからその素数は `2`. -/
theorem card_mulAut_eq_two_of_isSimpleGroup (hs : IsSimpleGroup (MulAut A))
    (h : ∃ a : A, a ^ 2 ≠ 1) : Nat.card (MulAut A) = 2 := by
  have hne : invMulAut A ≠ 1 := by
    intro hc
    obtain ⟨a, ha⟩ := h
    exact ha (invMulAut_eq_one_iff.mp hc a)
  have hcenter : Subgroup.center (MulAut A) = ⊤ := by
    rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center (MulAut A)) inferInstance with hb | ht
    · exact absurd (Subgroup.mem_bot.mp (hb ▸ invMulAut_mem_center (A := A))) hne
    · exact ht
  haveI : IsMulCommutative (MulAut A) := Subgroup.center_eq_top_iff.mp hcenter
  have hp : (Nat.card (MulAut A)).Prime := Group.is_simple_iff_prime_card.mp hs
  haveI : Finite (MulAut A) := Nat.finite_of_card_ne_zero hp.ne_zero
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf (invMulAut A) = 2 :=
    orderOf_eq_prime (by rw [pow_two, invMulAut_sq]) hne
  have hdvd : (2 : ℕ) ∣ Nat.card (MulAut A) := hord ▸ orderOf_dvd_natCard _
  exact ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp hdvd).symm

/-! ## The unit power maps embed `(ZMod n)ˣ` -/

/-- 指数が `n` を割る可換群では, `ZMod n` のスカラー倍は代表元による冪写像. -/
theorem zmod_smul_ofMul {n : ℕ} [NeZero n] [Module (ZMod n) (Additive A)] (c : ZMod n) (a : A) :
    c • (Additive.ofMul a) = Additive.ofMul (a ^ c.val) := by
  conv_lhs => rw [show c = ((c.val : ℕ) : ZMod n) from (ZMod.natCast_rightInverse c).symm]
  rw [Nat.cast_smul_eq_nsmul, ← ofMul_pow]

section Exponent

variable [Finite A]

/-- `Additive A` の `ZMod n`-加群構造と位数ちょうど `n` の元があれば `φ(n) ≤ |Aut(A)|`.

単元 `u : (ZMod n)ˣ` によるスカラー倍 (= 冪写像 `a ↦ a ^ u`) は自己同型
(`LinearEquiv.smulOfUnit` を `mulAutEquivLinearEquiv` で戻す) で, 位数 `n` の元の上で
値が一致すれば `u` が一致するから, `(ZMod n)ˣ → Aut(A)` は単射. -/
theorem totient_le_card_mulAut_of_orderOf_eq {n : ℕ} [NeZero n]
    [Module (ZMod n) (Additive A)] {g : A} (hg : orderOf g = n) :
    Nat.totient n ≤ Nat.card (MulAut A) := by
  classical
  have e : MulAut A ≃* (Additive A ≃ₗ[ZMod n] Additive A) := mulAutEquivLinearEquiv (n := n)
  set F : (ZMod n)ˣ → MulAut A := fun u =>
    e.symm (LinearEquiv.smulOfUnit (R := ZMod n) (M := Additive A) u) with hF
  have hinj : Function.Injective F := by
    intro u v huv
    have h1 : LinearEquiv.smulOfUnit (R := ZMod n) (M := Additive A) u
        = LinearEquiv.smulOfUnit (R := ZMod n) (M := Additive A) v :=
      e.symm.injective huv
    have h2 : (u : ZMod n) • (Additive.ofMul g) = (v : ZMod n) • (Additive.ofMul g) :=
      congrArg (fun e : Additive A ≃ₗ[ZMod n] Additive A => e (Additive.ofMul g)) h1
    rw [zmod_smul_ofMul, zmod_smul_ofMul] at h2
    have h3 : g ^ ((u : ZMod n).val) = g ^ ((v : ZMod n).val) := congrArg Additive.toMul h2
    have h4 : (u : ZMod n).val ≡ (v : ZMod n).val [MOD n] := by
      have := pow_eq_pow_iff_modEq.mp h3
      rwa [hg] at this
    have h5 : (u : ZMod n).val = (v : ZMod n).val := by
      have hu := ZMod.val_lt (u : ZMod n)
      have hv := ZMod.val_lt (v : ZMod n)
      simpa [Nat.ModEq, Nat.mod_eq_of_lt hu, Nat.mod_eq_of_lt hv] using h4
    exact Units.ext (ZMod.val_injective n h5)
  have hcard : Nat.card ((ZMod n)ˣ) = n.totient := by
    haveI : Fintype (ZMod n) := ZMod.fintype n
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
  calc n.totient = Nat.card ((ZMod n)ˣ) := hcard.symm
    _ ≤ Nat.card (MulAut A) := Nat.card_le_card_of_injective F hinj

/-- **`φ(exp A) ≤ |Aut(A)|`** (有限可換 `A`).

指数 `n` に対し `Additive A` は `ZMod n`-加群 (`zmodModule_of_pow_eq_one`) で,
位数ちょうど `n` の元が存在する (`Monoid.exists_orderOf_eq_exponent`) から
`totient_le_card_mulAut_of_orderOf_eq` が使える. -/
theorem totient_exponent_le_card_mulAut :
    Nat.totient (Monoid.exponent A) ≤ Nat.card (MulAut A) := by
  letI : Module (ZMod (Monoid.exponent A)) (Additive A) :=
    zmodModule_of_pow_eq_one (n := Monoid.exponent A) (E := A) fun x =>
      Monoid.pow_exponent_eq_one x
  obtain ⟨g, hg⟩ := Monoid.exists_orderOf_eq_exponent (G := A) Monoid.ExponentExists.of_finite
  exact totient_le_card_mulAut_of_orderOf_eq hg

/-! ## `φ(n) ≤ 2` の解 -/

/-- **`φ(n) ≤ 2` をみたす `n ≠ 0` は `1, 2, 3, 4, 6` のみ** (古典的).

`d ∣ n` なら `φ d ∣ φ n` (`Nat.totient_dvd_of_dvd`) なので, どの約数も `φ ≤ 2`.
`φ 8 = 4`, `φ 9 = 6`, `φ p = p - 1` から `8 ∤ n`, `9 ∤ n`, 素因数は `≤ 3`; したがって
`n ∣ 12` で, 残りは有限チェック (`12` 自身は `φ 12 = 4` で落ちる). -/
theorem eq_of_totient_le_two {n : ℕ} (hn : n ≠ 0) (h : n.totient ≤ 2) :
    n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 6 := by
  have hpos : 0 < n.totient := Nat.totient_pos.mpr (Nat.pos_of_ne_zero hn)
  have key : ∀ d : ℕ, d ∣ n → d.totient ≤ 2 := fun d hd =>
    le_trans (Nat.le_of_dvd hpos (Nat.totient_dvd_of_dvd hd)) h
  have h8 : ¬ (8 ∣ n) := fun hd => by have := key 8 hd; revert this; decide
  have h9 : ¬ (9 ∣ n) := fun hd => by have := key 9 hd; revert this; decide
  have hdvd : n ∣ 12 := by
    rw [Nat.dvd_iff_prime_pow_dvd_dvd]
    intro p k hp hpk
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    have hpn : p ∣ n := dvd_trans (dvd_pow_self p hk.ne') hpk
    have hp3 : p ≤ 3 := by
      have := key p hpn
      rw [Nat.totient_prime hp] at this
      have := hp.two_le
      omega
    have hp2 := hp.two_le
    interval_cases p
    · -- `p = 2`: `8 ∤ n` から `k ≤ 2`
      have hk2 : k ≤ 2 := by
        by_contra hc
        exact h8 (dvd_trans (pow_dvd_pow 2 (by omega : 3 ≤ k)) hpk)
      exact dvd_trans (pow_dvd_pow 2 hk2) (by norm_num)
    · -- `p = 3`: `9 ∤ n` から `k ≤ 1`
      have hk1 : k ≤ 1 := by
        by_contra hc
        exact h9 (dvd_trans (pow_dvd_pow 3 (by omega : 2 ≤ k)) hpk)
      exact dvd_trans (pow_dvd_pow 3 hk1) (by norm_num)
  have hle : n ≤ 12 := Nat.le_of_dvd (by norm_num) hdvd
  have hge : 1 ≤ n := Nat.pos_of_ne_zero hn
  interval_cases n <;> revert h <;> decide

/-- **有限可換群 `A` の自己同型群が単純で指数が `2` より大きいなら, 指数は `3`, `4`, `6`.**

単純性から `|Aut(A)| = 2` (`card_mulAut_eq_two_of_isSimpleGroup`), 単元冪写像の埋め込みから
`φ(exp A) ≤ 2` (`totient_exponent_le_card_mulAut`), あとは `eq_of_totient_le_two`. -/
theorem exponent_mem_of_isSimpleGroup_mulAut (hs : IsSimpleGroup (MulAut A))
    (h : ∃ a : A, a ^ 2 ≠ 1) :
    Monoid.exponent A = 3 ∨ Monoid.exponent A = 4 ∨ Monoid.exponent A = 6 := by
  have hcard := card_mulAut_eq_two_of_isSimpleGroup hs h
  have hle : Nat.totient (Monoid.exponent A) ≤ 2 := by
    rw [← hcard]; exact totient_exponent_le_card_mulAut
  have hpow : ∀ a : A, a ^ Monoid.exponent A = 1 := Monoid.pow_exponent_eq_one
  obtain ⟨a, ha⟩ := h
  rcases eq_of_totient_le_two Monoid.exponent_ne_zero_of_finite hle with he | he | he | he | he
  · exact absurd (by have := hpow a; rw [he, pow_one] at this; rw [this]; simp) ha
  · exact absurd (by have := hpow a; rwa [he] at this) ha
  · exact Or.inl he
  · exact Or.inr (Or.inl he)
  · exact Or.inr (Or.inr he)

end Exponent

end OddOrder.GroupTheory
