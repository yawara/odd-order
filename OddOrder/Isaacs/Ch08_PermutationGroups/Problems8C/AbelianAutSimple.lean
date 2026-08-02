/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.LinearGroupSimple
import OddOrder.GroupTheory.ElementaryAbelianLinear
import Mathlib.FieldTheory.Finiteness
import Mathlib.Algebra.Field.ZMod

/-!
# Isaacs, Finite Group Theory — Problem 8C.6, the elementary abelian half (p. 257)

Isaacs, *Finite Group Theory* (AMS GSM 92, 2008), Problem 8C.6 (書籍 p. 257):

> Let `A` be an abelian group.  Show that `Aut(A)` is simple if and only if `A` has order
> `3` or `A` is an elementary abelian `2`-group of order at least `8`.

This file supplies the second half of "⟸": an elementary abelian `2`-group of order at
least `8` has simple automorphism group.  (The `|A| = 3` half is
`isSimpleGroup_mulAut_of_card_eq_three` in `AbelianAut.lean`; "⟹" is still open.)

`Additive A` is a vector space over `𝔽₂` and `Aut(A)` is its linear group
(`mulAutEquivLinearEquiv`), of dimension `≥ 3` because `|A| = 2^dim ≥ 8`; then
`isSimpleGroup_linearEquiv` — Iwasawa's criterion with the transvection subgroups — gives
simplicity.
-/

set_option autoImplicit false

namespace OddOrder.Isaacs.Ch08

open OddOrder.GroupTheory

/-- `𝔽₂` の元は `0` か `1`. -/
theorem zmod_two_eq_zero_or_one (x : ZMod 2) : x = 0 ∨ x = 1 := by revert x; decide

/-- **Isaacs Problem 8C.6** の「⟸」その 2 (p. 257): 位数 `8` 以上の初等可換 `2`-群 `A` の
自己同型群は単純。

`Additive A` を `𝔽₂` 上のベクトル空間と見ると `Aut(A)` はその線形群
(`mulAutEquivLinearEquiv`)、`|A| = 2^dim ≥ 8` から次元は `3` 以上、あとは Iwasawa 判定
(`isSimpleGroup_linearEquiv`)。 -/
theorem isSimpleGroup_mulAut_of_elementaryAbelian_two {A : Type*} [CommGroup A] [Finite A]
    (hexp : ∀ x : A, x ^ 2 = 1) (hcard : 8 ≤ Nat.card A) : IsSimpleGroup (MulAut A) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : Module (ZMod 2) (Additive A) := zmodModule_of_pow_eq_one (n := 2) hexp
  haveI : Finite (Additive A) := inferInstanceAs (Finite A)
  haveI : Module.Finite (ZMod 2) (Additive A) := Module.Finite.of_finite
  have hK : ∀ x : ZMod 2, x = 0 ∨ x = 1 := zmod_two_eq_zero_or_one
  -- `|A| = 2 ^ dim`, so `dim ≥ 3`
  have hcardAdd : Nat.card (Additive A) = 2 ^ Module.finrank (ZMod 2) (Additive A) := by
    haveI := Fintype.ofFinite (Additive A)
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 2) (V := Additive A),
      ZMod.card]
  have hcardEq : Nat.card (Additive A) = Nat.card A :=
    Nat.card_congr (Additive.toMul (α := A))
  have h3 : 3 ≤ Module.finrank (ZMod 2) (Additive A) := by
    by_contra hcon
    have hle : (2 : ℕ) ^ Module.finrank (ZMod 2) (Additive A) ≤ 2 ^ 2 :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  haveI := isSimpleGroup_linearEquiv (K := ZMod 2) (V := Additive A) hK h3
  exact (mulAutEquivLinearEquiv (n := 2) (E := A)).isSimpleGroup


/-! ## ⚠ 書籍の「⟹」は偽 — 反例 `A = ℤ/4`

Isaacs Problem 8C.6 は「`Aut(A)` 単純 ⟺ `|A| = 3` または `A` が位数 8 以上の初等可換
2-群」と述べるが、**「⟹」は反例をもつ**: `A = ℤ/4` は巡回群なので
`|Aut(A)| = φ(4) = 2` で `Aut(A)` は単純、しかし `|A| = 4 ≠ 3` で `A` は位数 4 の元を
もつから初等可換 2-群でもない。(`ℤ/6` も同様: `φ(6) = 2`。)

正しい分類は — `Aut(A)` が可換な単純群 `≅ ℤ/2` になるのは
`A ∈ {ℤ/3, ℤ/4, ℤ/6}` のちょうど 3 つ (古典的な `φ(n) = 2` の解)、
非可換単純になるのは `A` が位数 8 以上の初等可換 2-群のとき (`GL(n,2)`, `n ≥ 3`)。
書籍の主張は前者の 3 つのうち `ℤ/3` しか挙げていない。
-/

/-- **⚠ Isaacs Problem 8C.6 の「⟹」の反例** — `A = ℤ/4` (乗法記法) は
`Aut(A)` が単純だが位数 `3` でも初等可換 `2`-群でもない。

`ℤ/4` は巡回なので `|Aut(A)| = φ(4) = 2` は素数、よって `Aut(A)` は単純
(`isSimpleGroup_of_prime_card`)。一方 `A` には位数 4 の元があるので `x ^ 2 ≠ 1`。 -/
theorem exists_isSimpleGroup_mulAut_not_card_three_not_elementaryAbelian :
    ∃ (A : Type) (_ : CommGroup A) (_ : Finite A),
      IsSimpleGroup (MulAut A) ∧ Nat.card A ≠ 3 ∧ ∃ x : A, x ^ 2 ≠ 1 := by
  classical
  refine ⟨Multiplicative (ZMod 4), inferInstance, inferInstance, ?_, ?_, ?_⟩
  · haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine isSimpleGroup_of_prime_card (p := 2) ?_
    rw [IsCyclic.card_mulAut]
    have hcard : Nat.card (Multiplicative (ZMod 4)) = 4 := by
      rw [Nat.card_eq_fintype_card]
      exact ZMod.card 4
    rw [hcard]
    decide
  · have hcard : Nat.card (Multiplicative (ZMod 4)) = 4 := by
      rw [Nat.card_eq_fintype_card]
      exact ZMod.card 4
    omega
  · refine ⟨Multiplicative.ofAdd (1 : ZMod 4), ?_⟩
    intro hc
    rw [pow_two, ← ofAdd_add] at hc
    have hz : (1 + 1 : ZMod 4) = 0 := by
      simpa using congrArg Multiplicative.toAdd hc
    exact absurd hz (by decide)

end OddOrder.Isaacs.Ch08
