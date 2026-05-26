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

/-- A noncyclic finite group of order `p^2` is elementary abelian. -/
theorem of_card_prime_sq_of_not_isCyclic
    [Finite G] (hp : p.Prime) (hCard : Nat.card G = p ^ 2)
    (hNotCyclic : ¬ IsCyclic G) :
    IsElementaryAbelian p G := by
  letI : Fact p.Prime := ⟨hp⟩
  have hExp : Monoid.exponent G = p :=
    (not_isCyclic_iff_exponent_eq_prime hp hCard).mp hNotCyclic
  refine ⟨IsPGroup.commutative_of_card_eq_prime_sq (p := p) hCard, ?_⟩
  intro x
  simpa [hExp] using (Monoid.pow_exponent_eq_one x)

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

/-- An elementary abelian group of order `p^2` has at least two distinct subgroups of order `p`.
-/
theorem exists_distinct_subgroups_card_prime_of_card_prime_sq
    [Finite G] (hp : p.Prime) (h : IsElementaryAbelian p G)
    (hCard : Nat.card G = p ^ 2) :
    ∃ H K : Subgroup G, Nat.card H = p ∧ Nat.card K = p ∧ H ≠ K := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hNotCyclic : ¬ IsCyclic G := h.not_isCyclic_of_card_prime_sq hp hCard
  have hCard_gt_one : 1 < Nat.card G := by
    rw [hCard]
    exact one_lt_pow₀ hp.one_lt two_ne_zero
  haveI : Nontrivial G := Finite.one_lt_card_iff_nontrivial.mp hCard_gt_one
  obtain ⟨x, hx_ne⟩ := exists_ne (1 : G)
  let H : Subgroup G := Subgroup.zpowers x
  have hx_order : orderOf x = p := orderOf_eq_prime (h.pow_eq_one x) hx_ne
  have hH_card : Nat.card H = p := by
    rw [show H = Subgroup.zpowers x from rfl, Nat.card_zpowers, hx_order]
  have hH_ne_top : H ≠ ⊤ := by
    intro hH_top
    exact hNotCyclic ((isCyclic_iff_exists_zpowers_eq_top (α := G)).mpr ⟨x, hH_top⟩)
  have h_exists_not_mem : ∃ y : G, y ∉ H := by
    by_contra hAll
    apply hH_ne_top
    ext y
    constructor
    · intro hy
      exact Subgroup.mem_top y
    · intro _hy
      by_contra hyH
      exact hAll ⟨y, hyH⟩
  obtain ⟨y, hy_not_mem⟩ := h_exists_not_mem
  let K : Subgroup G := Subgroup.zpowers y
  have hy_ne : y ≠ 1 := by
    intro hy
    exact hy_not_mem (hy ▸ H.one_mem)
  have hy_order : orderOf y = p := orderOf_eq_prime (h.pow_eq_one y) hy_ne
  have hK_card : Nat.card K = p := by
    rw [show K = Subgroup.zpowers y from rfl, Nat.card_zpowers, hy_order]
  refine ⟨H, K, hH_card, hK_card, ?_⟩
  intro hHK
  exact hy_not_mem (hHK ▸ Subgroup.mem_zpowers y)

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

/-- An elementary abelian subgroup of order `p^2` contains two distinct ambient subgroups of
order `p`. -/
theorem exists_distinct_subgroups_card_prime_of_isElementaryAbelian_card_prime_sq
    {H : Subgroup G} [Finite H] {p : ℕ} (hp : p.Prime)
    (hH : H.IsElementaryAbelian p) (hCard : Nat.card H = p ^ 2) :
    ∃ K L : Subgroup G, K ≤ H ∧ L ≤ H ∧
      Nat.card K = p ∧ Nat.card L = p ∧ K ≠ L := by
  obtain ⟨K₀, L₀, hK₀_card, hL₀_card, hK₀L₀_ne⟩ :=
    hH.exists_distinct_subgroups_card_prime_of_card_prime_sq hp hCard
  let K : Subgroup G := K₀.map H.subtype
  let L : Subgroup G := L₀.map H.subtype
  have hK_card : Nat.card K = p := by
    rw [show K = K₀.map H.subtype from rfl,
      Subgroup.card_map_of_injective H.subtype_injective, hK₀_card]
  have hL_card : Nat.card L = p := by
    rw [show L = L₀.map H.subtype from rfl,
      Subgroup.card_map_of_injective H.subtype_injective, hL₀_card]
  have hKL_ne : K ≠ L := by
    intro hKL
    exact hK₀L₀_ne (Subgroup.map_injective H.subtype_injective hKL)
  exact ⟨K, L, Subgroup.map_subtype_le K₀, Subgroup.map_subtype_le L₀,
    hK_card, hL_card, hKL_ne⟩

/-- If `G` contains an elementary abelian subgroup of order `p^2`, then `G` contains two
distinct subgroups of order `p`. -/
theorem exists_distinct_subgroups_card_prime_of_exists_isElementaryAbelian_card_prime_sq
    {p : ℕ} (hp : p.Prime)
    (hExists : ∃ H : Subgroup G, H.IsElementaryAbelian p ∧ Nat.card H = p ^ 2) :
    ∃ K L : Subgroup G, Nat.card K = p ∧ Nat.card L = p ∧ K ≠ L := by
  obtain ⟨H, hH_elem, hH_card⟩ := hExists
  haveI : Finite H := Nat.finite_of_card_ne_zero (by
    rw [hH_card]
    exact pow_ne_zero 2 hp.ne_zero)
  obtain ⟨K, L, _hK_le, _hL_le, hK_card, hL_card, hKL_ne⟩ :=
    exists_distinct_subgroups_card_prime_of_isElementaryAbelian_card_prime_sq
      hp hH_elem hH_card
  exact ⟨K, L, hK_card, hL_card, hKL_ne⟩

/-- If `G` has at most one subgroup of order `p`, then it contains no elementary abelian
subgroup of order `p^2`. -/
theorem not_exists_isElementaryAbelian_card_prime_sq_of_subgroups_card_prime_unique
    {p : ℕ} (hp : p.Prime)
    (hUnique : ∀ K L : Subgroup G, Nat.card K = p → Nat.card L = p → K = L) :
    ¬ ∃ H : Subgroup G, H.IsElementaryAbelian p ∧ Nat.card H = p ^ 2 := by
  intro hExists
  obtain ⟨K, L, hK_card, hL_card, hKL_ne⟩ :=
    exists_distinct_subgroups_card_prime_of_exists_isElementaryAbelian_card_prime_sq
      hp hExists
  exact hKL_ne (hUnique K L hK_card hL_card)

end Subgroup
