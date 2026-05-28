/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.RepresentationTheory.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.GroupTheory.OrderOfElement

/-!
# Coprime action — trivial step

`OddOrder.GroupTheory.RepresentationTheory.CoprimeActionTrivial`: BG App.A (A.3) で使う
**coprime action 補題の単段版**.

## Main result

`coprime_action_trivial_step`: 有限群 `G` が表現 `ρ : Representation F G V` で `V` に作用,
`|G|` が `F` 上可逆 (`NeZero (Nat.card G : F)`, ⇔ char `F` ∤ `|G|`) のとき,
`G`-不変部分空間 `W ≤ V` で `G` が `W` 上 + `V/W` 上自明に作用するなら `G` は `V` 全体に
自明に作用する.

これは Gorenstein FG 1968 Thm 3.4 (coprime action ⇒ 商上自明から全体自明への持ち上げ)
の単段版. 合成列 (`CompositionSeries`) 上で帰納適用すれば「全 composition factor 上自明
⇒ 全体自明」が出る (合成列版は別ファイル).

## 証明戦略 (Maschke 不要, 直接展開)

`T := ρ g - 1 : End_F V` とおくと:

* `T(V) ⊆ W` (G triv on V/W)
* `T|_W = 0` (G triv on W)
* ∴ `T² = 0`

このとき二項展開 `(1 + T)^n = 1 + n • T` (`T² = 0` 系で `T^i = 0`, i ≥ 2).
`m := orderOf g`, `(ρ g)^m = 1` より `1 = 1 + m • T`, ∴ `m • T = 0`.
`m ∣ |G|` かつ `(|G| : F) ≠ 0` で `(m : F) ≠ 0`, よって `T = 0`, `ρ g = 1`. ∎

## 用途

* `OddOrder/BG/AppA_PStability.lean` の `thmA3` (BG Thm A.3) 証明 Step 5
  (= H に p'-元 ⇒ V 上自明 ⇒ ρ faithful と矛盾).
-/

namespace OddOrder.GroupTheory.RepresentationTheory

section TrivialStep

variable {F : Type*} [Field F]
variable {V : Type*} [AddCommGroup V] [Module F V]
variable {G : Type*} [Group G] [Finite G]

/-- `(1 + T)^n = 1 + n • T` when `T * T = 0` in a semiring. -/
private lemma sq_zero_one_add_pow {R : Type*} [Semiring R] {T : R} (hT : T * T = 0) :
    ∀ n : ℕ, (1 + T) ^ n = 1 + n • T
  | 0 => by simp
  | n + 1 => by
      rw [pow_succ, sq_zero_one_add_pow hT n]
      have hsmul : (n : ℕ) • T * T = 0 := by
        rw [nsmul_eq_mul, mul_assoc, hT, mul_zero]
      have hexpand : (1 + (n : ℕ) • T) * (1 + T) =
          1 + T + (n : ℕ) • T + (n : ℕ) • T * T := by
        rw [mul_add, mul_one, add_mul, one_mul]
        abel
      rw [hexpand, hsmul, add_zero, succ_nsmul]
      abel

omit [Finite G] in
/-- **Coprime action — trivial step**: 有限群 `G` が `V` に `ρ` で作用し `|G|` が
`F` 上可逆なとき, `G`-不変 `W ≤ V` 上 + 商 `V/W` 上で `G` が自明に作用すれば
`G` は `V` 全体に自明に作用する.

仮定:
* `[NeZero (Nat.card G : F)]`: `(|G| : F) ≠ 0`, char `F` が `|G|` を割らない (=
  `G` が char `F` に coprime). char 0 でも成立.
* `hW_inv`: `W` は `G`-不変.
* `hW_triv`: `G` は `W` 上自明 (任意の `w ∈ W` で `ρ g w = w`).
* `hVW_triv`: `G` は `V/W` 上自明 (任意の `v ∈ V`, `ρ g v - v ∈ W`).

結論: `ρ g v = v` (任意の `g ∈ G`, `v ∈ V`).

証明: `T := ρ g - 1` で `T² = 0` を示し, `(1 + T)^(orderOf g) = (ρ g)^(orderOf g) = 1`
を二項展開して `(orderOf g) • T = 0` を得る. `orderOf g ∣ |G|` と `(|G| : F) ≠ 0`
から `(orderOf g : F) ≠ 0`, F は体なので `T = 0`. -/
theorem coprime_action_trivial_step
    (ρ : Representation F G V) [NeZero (Nat.card G : F)]
    {W : Submodule F V}
    (_hW_inv : ∀ g (w : V), w ∈ W → ρ g w ∈ W)
    (hW_triv : ∀ g (w : V), w ∈ W → ρ g w = w)
    (hVW_triv : ∀ g (v : V), ρ g v - v ∈ W) :
    ∀ (g : G) (v : V), ρ g v = v := by
  intro g v
  -- Step 1: T := ρ g - 1 has T² = 0 (= T * T = 0).
  set T : Module.End F V := (ρ g : Module.End F V) - 1 with hT_def
  have hT_sq : T * T = 0 := by
    ext u
    -- Goal: (T * T) u = 0; (T * T) u = T (T u) since End mult = composition.
    have hTu_mem : T u ∈ W := by
      change ρ g u - u ∈ W
      exact hVW_triv g u
    have hT_TuVal : T (T u) = ρ g (T u) - T u := by
      change (ρ g : Module.End F V) (T u) - (1 : Module.End F V) (T u) = _
      rw [Module.End.one_apply]
    change T (T u) = (0 : Module.End F V) u
    rw [hT_TuVal, hW_triv g _ hTu_mem]
    simp
  -- Step 2: (1 + T)^m = 1 + m • T (binomial で T² = 0 系).
  set m : ℕ := orderOf g with hm_def
  have h_one_add_T : (1 : Module.End F V) + T = (ρ g : Module.End F V) := by
    rw [hT_def]; abel
  have h_pow_eq : (1 + T) ^ m = 1 + m • T := sq_zero_one_add_pow hT_sq m
  -- Step 3: (1 + T)^m = ρ(g^m) = 1.
  have h_pow_one : (1 + T) ^ m = 1 := by
    rw [h_one_add_T]
    have h_pow : (ρ g : Module.End F V) ^ m = ρ (g ^ m) := (map_pow ρ g m).symm
    rw [h_pow, hm_def, pow_orderOf_eq_one g, map_one]
  -- Step 4: m • T = 0 (from h_pow_eq + h_pow_one).
  have h_m_T : (m : ℕ) • T = 0 := by
    have h_eq : (1 : Module.End F V) + m • T = 1 := h_pow_eq.symm.trans h_pow_one
    have := add_left_cancel (h_eq.trans (add_zero (1 : Module.End F V)).symm)
    exact this
  -- Step 5: (m : F) ≠ 0 から T = 0.
  have hm_dvd : m ∣ Nat.card G := orderOf_dvd_natCard g
  have h_m_ne_zero : (m : F) ≠ 0 := by
    intro h_zero
    apply NeZero.ne (Nat.card G : F)
    obtain ⟨k, hk⟩ := hm_dvd
    rw [hk, Nat.cast_mul, h_zero, zero_mul]
  -- (m : F) • T = m • T = 0
  have h_smul_T : (m : F) • T = 0 := by
    rw [Nat.cast_smul_eq_nsmul, h_m_T]
  -- F is a field, m ≠ 0 in F, so T = 0.
  have hT_zero : T = 0 := by
    rcases smul_eq_zero.mp h_smul_T with h | h
    · exact absurd h h_m_ne_zero
    · exact h
  -- Step 6: ρ g v - v = T v = 0, so ρ g v = v.
  have hTv : T v = 0 := by rw [hT_zero]; rfl
  have h_diff : ρ g v - v = 0 := by
    have hTv' : ((ρ g : Module.End F V) - 1) v = 0 := hTv
    rw [LinearMap.sub_apply, Module.End.one_apply] at hTv'
    exact hTv'
  exact sub_eq_zero.mp h_diff

end TrivialStep

end OddOrder.GroupTheory.RepresentationTheory
