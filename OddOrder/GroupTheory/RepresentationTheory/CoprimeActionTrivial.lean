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

/-! ## Relative + chain version

`coprime_action_trivial_step` を `U ≤ V` 上に拡張し、合成列 (chain) に沿って下降帰納で
適用するための補題群.

* `coprime_action_trivial_relative_step`: `W ≤ U ≤ V` で `G` が `W` 上自明 + `U` 上で
  `ρ g u - u ∈ W` (= `U/W` 上自明) なら `G` は `U` 上自明.
* `coprime_action_trivial_chain`: chain `s : Fin (n+1) → Submodule F V` で `s 0 = ⊥`,
  `s last = ⊤`, 各 quotient 上自明 ⇒ `V` 全体自明. -/

section RelativeStep

variable {F : Type*} [Field F]
variable {V : Type*} [AddCommGroup V] [Module F V]
variable {G : Type*} [Group G] [Finite G]

/-- Aux: `T w = 0` なら `(1 + T)^n w = w` (`w` 上 `1+T` 恒等). -/
private lemma pow_one_add_apply_of_apply_zero
    (T : Module.End F V) {w : V} (hTw : T w = 0) :
    ∀ n : ℕ, (((1 : Module.End F V) + T) ^ n) w = w := by
  intro n
  induction n with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Module.End.mul_apply]
    have h_one_add_w : ((1 : Module.End F V) + T) w = w := by
      rw [LinearMap.add_apply, Module.End.one_apply, hTw, add_zero]
    rw [h_one_add_w, ih]

/-- Aux: `T (T u) = 0` なら `(1 + T)^n u = u + n • T u` (pointwise binomial). -/
private lemma pow_one_add_apply_of_apply_apply_zero
    (T : Module.End F V) {u : V} (hT2u : T (T u) = 0) :
    ∀ n : ℕ, (((1 : Module.End F V) + T) ^ n) u = u + n • T u := by
  intro n
  induction n with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Module.End.mul_apply]
    have h_one_add_u : ((1 : Module.End F V) + T) u = u + T u := by
      rw [LinearMap.add_apply, Module.End.one_apply]
    rw [h_one_add_u, map_add, ih,
        pow_one_add_apply_of_apply_zero T hT2u k, succ_nsmul]
    abel

omit [Finite G] in
/-- **Relative coprime action step**: `W ≤ U ≤ V` (両 `Submodule F V`),
`G` が `W` 上自明 (`∀ g w ∈ W, ρ g w = w`) かつ `U` 上で「mod W で自明」
(`∀ g u ∈ U, ρ g u - u ∈ W`) なら `G` は `U` 上自明.

`coprime_action_trivial_step` の "U = ⊤" 一般化. 仮定 `[NeZero (Nat.card G : F)]`
は同じ ((|G| : F) ≠ 0).

証明: pointwise 版 binomial. `T := ρ g - 1`, `u ∈ U` で `T u ∈ W` (mod W),
`T (T u) = 0` (`G` triv on `W`), `(1+T)^m u = u + m • T u` で `m • T u = 0`,
`(m : F) ≠ 0` で `T u = 0` ⇒ `ρ g u = u`. -/
theorem coprime_action_trivial_relative_step
    (ρ : Representation F G V) [NeZero (Nat.card G : F)]
    {W U : Submodule F V}
    (hW_triv : ∀ (g : G) (w : V), w ∈ W → ρ g w = w)
    (hUW_triv : ∀ (g : G) (u : V), u ∈ U → ρ g u - u ∈ W) :
    ∀ (g : G) (u : V), u ∈ U → ρ g u = u := by
  intro g u huU
  set T : Module.End F V := (ρ g : Module.End F V) - 1 with hT_def
  have hTu : T u ∈ W := by
    change ρ g u - u ∈ W
    exact hUW_triv g u huU
  have hT2u : T (T u) = 0 := by
    have h1 : ρ g (T u) = T u := hW_triv g _ hTu
    change ((ρ g : Module.End F V) - 1) (T u) = 0
    rw [LinearMap.sub_apply, Module.End.one_apply, h1, sub_self]
  set m : ℕ := orderOf g with hm_def
  have h_pow_apply : (((1 : Module.End F V) + T) ^ m) u = u + m • T u :=
    pow_one_add_apply_of_apply_apply_zero T hT2u m
  have h_one_add_T : (1 : Module.End F V) + T = (ρ g : Module.End F V) := by
    rw [hT_def]; abel
  have h_pow_one : (((1 : Module.End F V) + T) ^ m) u = u := by
    rw [h_one_add_T]
    have hpow : (ρ g : Module.End F V) ^ m = ρ (g ^ m) := (map_pow ρ g m).symm
    rw [hpow, hm_def, pow_orderOf_eq_one, map_one, Module.End.one_apply]
  have h_m_T_u : m • T u = 0 := by
    have h_eq : u + m • T u = u := h_pow_apply.symm.trans h_pow_one
    have := h_eq.trans (add_zero u).symm
    exact add_left_cancel this
  have hm_dvd : m ∣ Nat.card G := orderOf_dvd_natCard g
  have h_m_ne_zero : (m : F) ≠ 0 := by
    intro h_zero
    apply NeZero.ne (Nat.card G : F)
    obtain ⟨k, hk⟩ := hm_dvd
    rw [hk, Nat.cast_mul, h_zero, zero_mul]
  have h_smul_T_u : (m : F) • T u = 0 := by
    rw [Nat.cast_smul_eq_nsmul]; exact h_m_T_u
  have h_T_u_zero : T u = 0 := by
    rcases smul_eq_zero.mp h_smul_T_u with h | h
    · exact absurd h h_m_ne_zero
    · exact h
  have h_diff : (ρ g : Module.End F V) u - u = 0 := by
    have h1 : T u = (ρ g : Module.End F V) u - u := by
      change ((ρ g : Module.End F V) - 1) u = _
      rw [LinearMap.sub_apply, Module.End.one_apply]
    rw [← h1]; exact h_T_u_zero
  exact sub_eq_zero.mp h_diff

omit [Finite G] in
/-- **Coprime action — chain version**: chain `s : Fin (n+1) → Submodule F V`
で `s 0 = ⊥`, `s (Fin.last n) = ⊤`, 各 quotient 上 `G` 自明
(`∀ g v ∈ s i.succ, ρ g v - v ∈ s i.castSucc`) なら `G` は `V` 全体自明.

monotonicity (`s i.castSucc ≤ s i.succ`) は `h_triv_quot` から間接的に従う
(`ρ g v ∈ s i.succ` 経由) ので仮定不要.

証明: 上向き帰納で `∀ i, ∀ v ∈ s i, ρ g v = v`. base `s 0 = ⊥` で trivial,
step `s i → s (i+1)` は `coprime_action_trivial_relative_step` を `W = s i.castSucc`,
`U = s i.succ` で適用. -/
theorem coprime_action_trivial_chain
    (ρ : Representation F G V) [NeZero (Nat.card G : F)]
    {n : ℕ} (s : Fin (n + 1) → Submodule F V)
    (h_bot : s 0 = ⊥) (h_top : s (Fin.last n) = ⊤)
    (h_triv_quot : ∀ (g : G) (i : Fin n) (v : V),
        v ∈ s i.succ → ρ g v - v ∈ s i.castSucc) :
    ∀ (g : G) (v : V), ρ g v = v := by
  suffices h_key : ∀ (i : Fin (n + 1)) (g : G) (v : V), v ∈ s i → ρ g v = v by
    intro g v
    exact h_key (Fin.last n) g v (by rw [h_top]; trivial)
  intro i
  induction i using Fin.induction with
  | zero =>
    intro g v hv
    rw [h_bot] at hv
    rw [(Submodule.mem_bot _).mp hv, map_zero]
  | succ j ih =>
    intro g v hv
    exact coprime_action_trivial_relative_step ρ
      (W := s j.castSucc) (U := s j.succ)
      (fun g' w hw => ih g' w hw)
      (fun g' u hu => h_triv_quot g' j u hu) g v hv

end RelativeStep

end OddOrder.GroupTheory.RepresentationTheory
