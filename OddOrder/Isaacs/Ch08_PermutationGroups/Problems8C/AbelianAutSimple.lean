/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.LinearGroupSimple
import OddOrder.GroupTheory.ElementaryAbelianLinear
import OddOrder.GroupTheory.CommGroupAut
import Mathlib.FieldTheory.Finiteness
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
import Mathlib.LinearAlgebra.Dimension.Free

/-!
# Isaacs, Finite Group Theory — Problem 8C.6 (p. 257), the corrected classification

Isaacs, *Finite Group Theory* (AMS GSM 92, 2008), Problem 8C.6 (書籍 p. 257):

> Let `A` be an abelian group.  Show that `Aut(A)` is simple if and only if `A` has order
> `3` or `A` is an elementary abelian `2`-group of order at least `8`.

**⚠ 書籍の主張は「⟹」が偽**: `ℤ/4` と `ℤ/6` はどちらも `|Aut| = φ = 2` なので `Aut` は
単純だが, 位数 `3` でも初等可換 `2`-群でもない
(`exists_isSimpleGroup_mulAut_not_card_three_not_elementaryAbelian`).  正しい分類は

`isSimpleGroup_mulAut_iff` : 有限可換 `A` について `Aut(A)` 単純 ⟺
**`A` が位数 `3`, `4`, `6` の巡回群, または位数 `8` 以上の初等可換 `2`-群**.

本 leaf の構成:

* 初等可換 `2`-群側 (`isSimpleGroup_mulAut_of_elementaryAbelian_two`): `Additive A` を
  `𝔽₂` 上のベクトル空間と見ると (`mulAutEquivLinearEquiv`) `Aut(A)` はその線形群で,
  `|A| = 2^dim ≥ 8` から次元 `≥ 3`, あとは Iwasawa 判定 (`isSimpleGroup_linearEquiv`).
* `|A| < 8` の初等可換 `2`-群は除外される
  (`not_isSimpleGroup_mulAut_of_elementaryAbelian_two_of_card_lt_eight`): 次元 `≤ 1` なら
  `Aut(A)` が自明, 次元 `= 2` なら `|Aut(A)| = |GL(2,2)| = 6` (`card_linearEquiv_eq_six`).
* 指数 `> 2` 側は `OddOrder.GroupTheory.isCyclic_and_card_of_isSimpleGroup_mulAut`
  (中心的反転 ⟹ `|Aut| = 2` ⟹ 巡回 + `φ(|A|) = 2`).
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

正しい分類 (`isSimpleGroup_mulAut_iff`, 本 leaf 末尾) は — `Aut(A)` が可換な単純群
`≅ ℤ/2` になるのは `A` が位数 `3, 4, 6` の巡回群のとき (古典的な `φ(n) = 2` の解)、
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

/-! ## 小さい初等可換 `2`-群 — 位数 `4` では `Aut(A) ≅ S₃` -/

/-- **`2` 次元 `𝔽₂`-ベクトル空間の線形群は位数 `6`** (`|GL(2,2)| = 6`).

基底を取って `End(V) ≃ₐ Matrix (Fin 2) (Fin 2) 𝔽₂` (`algEquivMatrix`), 単元を取って
`GL(2, 𝔽₂)`, あとは `Matrix.card_GL_field` の
`∏ i : Fin 2, (2 ^ 2 - 2 ^ i) = 3 * 2`. -/
theorem card_linearEquiv_eq_six {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [Module.Finite (ZMod 2) V] (h : Module.finrank (ZMod 2) V = 2) :
    Nat.card (V ≃ₗ[ZMod 2] V) = 6 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let b : Module.Basis (Fin 2) (ZMod 2) V := Module.finBasisOfFinrankEq (ZMod 2) V h
  have e : (V ≃ₗ[ZMod 2] V) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 2) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V).symm.trans
      (Units.mapEquiv (algEquivMatrix b).toRingEquiv.toMulEquiv)
  rw [Nat.card_congr e.toEquiv, Matrix.card_GL_field]
  simp [Fin.prod_univ_two, ZMod.card]

/-- **位数 `8` 未満の初等可換 `2`-群の自己同型群は単純でない.**

次元 `≤ 1` なら `|A| ≤ 2` で `Aut(A)` は自明 (`subsingleton_mulAut_of_card_le_two`),
次元 `= 2` なら `|Aut(A)| = |GL(2,2)| = 6` で位数 `6` の群は単純でない
(`not_isSimpleGroup_of_card_eq_six`). -/
theorem not_isSimpleGroup_mulAut_of_elementaryAbelian_two_of_card_lt_eight {A : Type*}
    [CommGroup A] [Finite A] (hexp : ∀ x : A, x ^ 2 = 1) (hcard : Nat.card A < 8) :
    ¬ IsSimpleGroup (MulAut A) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : Module (ZMod 2) (Additive A) := zmodModule_of_pow_eq_one (n := 2) hexp
  haveI : Finite (Additive A) := inferInstanceAs (Finite A)
  haveI : Module.Finite (ZMod 2) (Additive A) := Module.Finite.of_finite
  intro hs
  have hcardAdd : Nat.card (Additive A) = 2 ^ Module.finrank (ZMod 2) (Additive A) := by
    haveI := Fintype.ofFinite (Additive A)
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 2) (V := Additive A),
      ZMod.card]
  have hcardEq : Nat.card (Additive A) = Nat.card A :=
    Nat.card_congr (Additive.toMul (α := A))
  have hd : Module.finrank (ZMod 2) (Additive A) ≤ 2 := by
    by_contra hc
    have hpow : (2 : ℕ) ^ 3 ≤ 2 ^ Module.finrank (ZMod 2) (Additive A) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  rcases Nat.lt_or_ge (Module.finrank (ZMod 2) (Additive A)) 2 with hlt | hge
  · have hA2 : Nat.card A ≤ 2 := by
      have hpow : (2 : ℕ) ^ Module.finrank (ZMod 2) (Additive A) ≤ 2 ^ 1 :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    haveI := subsingleton_mulAut_of_card_le_two hA2
    haveI := hs.toNontrivial
    exact false_of_nontrivial_of_subsingleton (MulAut A)
  · have hfr : Module.finrank (ZMod 2) (Additive A) = 2 := le_antisymm hd hge
    refine not_isSimpleGroup_of_card_eq_six ?_ hs
    rw [Nat.card_congr (mulAutEquivLinearEquiv (n := 2) (E := A)).toEquiv]
    exact card_linearEquiv_eq_six hfr

/-! ## Isaacs Problem 8C.6 — 訂正後の完全な分類 -/

/-- **Isaacs Problem 8C.6 の「⟸」その 3**: 位数 `3`, `4`, `6` の巡回群の自己同型群は単純
(`φ(3) = φ(4) = φ(6) = 2`). -/
theorem isSimpleGroup_mulAut_of_isCyclic_card {A : Type*} [CommGroup A] [Finite A] [IsCyclic A]
    (h : Nat.card A = 3 ∨ Nat.card A = 4 ∨ Nat.card A = 6) : IsSimpleGroup (MulAut A) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine isSimpleGroup_of_prime_card (p := 2) ?_
  rw [IsCyclic.card_mulAut]
  rcases h with h | h | h <;> rw [h] <;> decide

/-- **Isaacs Problem 8C.6 (訂正版)** — 有限可換群 `A` について

`Aut(A)` が単純 ⟺ `A` が位数 `3`, `4`, `6` の巡回群, または `A` が位数 `8` 以上の
初等可換 `2`-群.

⚠ 書籍 p. 257 の主張は「`|A| = 3` または位数 `8` 以上の初等可換 `2`-群」で,
`ℤ/4` と `ℤ/6` (どちらも `|Aut| = φ = 2`) が漏れている
(`exists_isSimpleGroup_mulAut_not_card_three_not_elementaryAbelian` が反例). -/
theorem isSimpleGroup_mulAut_iff {A : Type*} [CommGroup A] [Finite A] :
    IsSimpleGroup (MulAut A) ↔
      (IsCyclic A ∧ (Nat.card A = 3 ∨ Nat.card A = 4 ∨ Nat.card A = 6)) ∨
        ((∀ x : A, x ^ 2 = 1) ∧ 8 ≤ Nat.card A) := by
  constructor
  · intro hs
    by_cases hexp : ∀ x : A, x ^ 2 = 1
    · refine Or.inr ⟨hexp, ?_⟩
      by_contra hlt
      exact not_isSimpleGroup_mulAut_of_elementaryAbelian_two_of_card_lt_eight hexp
        (by omega) hs
    · refine Or.inl (isCyclic_and_card_of_isSimpleGroup_mulAut hs ?_)
      by_contra hc
      exact hexp fun x => not_not.mp fun hx => hc ⟨x, hx⟩
  · rintro (⟨hcyc, hc⟩ | ⟨hexp, hc⟩)
    · exact isSimpleGroup_mulAut_of_isCyclic_card hc
    · exact isSimpleGroup_mulAut_of_elementaryAbelian_two hexp hc

end OddOrder.Isaacs.Ch08
