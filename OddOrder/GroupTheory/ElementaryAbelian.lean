/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.Sylow

/-!
# Elementary Abelian Groups

`OddOrder.GroupTheory` shared module: 'elementary abelian p-group' の概念.

mathlib v4.29.1 にはこの概念 ("G abelian かつ ∀ x, x^p = 1") が無いため, 本リポジトリの
Ch.3 (Isaacs Thm 3.11), Ch.6 (6.9/6.15), Ch.7 (J(P) 定義) 共通の shared concept として
独立 module に切り出す. BG App.A, App.B (Puig L(S)) も将来再利用する.

## Main definitions

* `OddOrder.GroupTheory.IsElementaryAbelian p G`: 群 `G` が `p`-elementary abelian.
* `Subgroup.IsElementaryAbelian H p`: 部分群 `H ≤ G` が `p`-elementary abelian
  (whole-group form を `↥H` に適用; dot-notation friendly).

## Design notes

* `p` prime 仮定は def 段階では入れない (mathlib 慣用). 主結果記述時に `[Fact p.Prime]` 付与.
* def 形式は **(commute) ∧ (∀ x, x^p = 1)** を採用 (Ch.3 既存実装と整合). 別形式
  `IsPGroup p G ∧ Monoid.exponent G ∣ p` への bridge は将来追加可.
* 将来 mathlib upstream 視野で `OddOrder/Mathlib/ElementaryAbelian.lean` 候補.
-/

namespace OddOrder.GroupTheory

/-- **Elementary Abelian p-Group** (type-level): `G` is `p`-elementary abelian iff
`G` is abelian and `∀ x : G, x ^ p = 1`. -/
def IsElementaryAbelian (p : ℕ) (G : Type*) [Group G] : Prop :=
  (∀ x y : G, x * y = y * x) ∧ (∀ x : G, x ^ p = 1)

namespace IsElementaryAbelian

variable {p : ℕ} {G : Type*} [Group G]

/-- Commutativity projection. -/
theorem comm (h : IsElementaryAbelian p G) (x y : G) : x * y = y * x := h.1 x y

/-- `p`-th power projection. -/
theorem pow_eq_one (h : IsElementaryAbelian p G) (x : G) : x ^ p = 1 := h.2 x

/-- An elementary abelian `p`-group is a `p`-group. -/
theorem isPGroup (h : IsElementaryAbelian p G) : IsPGroup p G := fun x =>
  ⟨1, by simpa using h.pow_eq_one x⟩

/-- Subgroups of elementary abelian groups are elementary abelian. -/
theorem to_subgroup (h : IsElementaryAbelian p G) (H : Subgroup G) :
    IsElementaryAbelian p H := by
  refine ⟨?_, ?_⟩
  · intro x y
    ext
    exact h.comm (x : G) (y : G)
  · intro x
    ext
    exact h.pow_eq_one (x : G)

/-- A finite elementary abelian group of order `p^2` is not cyclic. -/
theorem not_isCyclic_of_card_prime_sq
    [Finite G] (hp : p.Prime) (h : IsElementaryAbelian p G)
    (hCard : Nat.card G = p ^ 2) :
    ¬ IsCyclic G := by
  intro hcyc
  haveI : IsCyclic G := hcyc
  have hExp_eq : Monoid.exponent G = Nat.card G := IsCyclic.exponent_eq_card
  have hExp_dvd_p : Monoid.exponent G ∣ p := by
    rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
    exact h.pow_eq_one
  rw [hCard] at hExp_eq
  rw [hExp_eq] at hExp_dvd_p
  have hp_lt_sq : p < p ^ 2 := by
    have hp_pow : p ^ 1 < p ^ 2 :=
      pow_lt_pow_right₀ hp.one_lt (by norm_num : (1 : ℕ) < 2)
    simpa using hp_pow
  exact (Nat.not_dvd_of_pos_of_lt hp.pos hp_lt_sq) hExp_dvd_p

/-- A finite elementary abelian group of cardinality at least `p^2` contains an elementary
abelian subgroup of order `p^2`. -/
theorem exists_subgroup_card_prime_sq
    [Finite G] (hp : p.Prime) (h : IsElementaryAbelian p G)
    (hCard : p ^ 2 ≤ Nat.card G) :
    ∃ H : Subgroup G, IsElementaryAbelian p H ∧ Nat.card H = p ^ 2 := by
  obtain ⟨H, hH_card⟩ :=
    Sylow.exists_subgroup_card_pow_prime_of_le_card (n := 2) hp h.isPGroup hCard
  exact ⟨H, h.to_subgroup H, hH_card⟩

end IsElementaryAbelian

end OddOrder.GroupTheory

namespace Subgroup

variable {G : Type*} [Group G]

/-- **Subgroup is Elementary Abelian**: subgroup `H ≤ G` is `p`-elementary abelian iff
the subtype `↥H` is `p`-elementary abelian as a group. -/
def IsElementaryAbelian (H : Subgroup G) (p : ℕ) : Prop :=
  OddOrder.GroupTheory.IsElementaryAbelian p ↥H

end Subgroup
